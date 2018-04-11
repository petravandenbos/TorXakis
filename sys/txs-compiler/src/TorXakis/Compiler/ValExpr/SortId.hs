{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
module TorXakis.Compiler.ValExpr.SortId where

import           Control.Arrow             (left, (|||))
import           Control.Monad             (when)
import           Control.Monad.Error.Class (liftEither)
import           Data.Either               (partitionEithers)
import           Data.List                 (intersect)
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Monoid               ((<>))
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import           Data.Traversable          (for)
import           GHC.Exts                  (fromList)

import           FuncId                    (funcargs, funcsort)
import           Id                        (Id (Id))
import           SortId                    (SortId (SortId), sortIdBool,
                                            sortIdInt, sortIdRegex,
                                            sortIdString)

import           TorXakis.Compiler.Data
import           TorXakis.Compiler.Error
import           TorXakis.Parser.Data

-- | Construct a list of sort ID's from a list of ADT declarations.
--
-- The ID of the ADT will coincide with the ID of the SortId.
compileToSortId :: [ADTDecl] -> CompilerM (Map Text SortId)
compileToSortId ds = Map.fromList . zip (adtName <$> ds) <$>
    traverse adtDeclToSortId ds

adtDeclToSortId :: ADTDecl -> CompilerM SortId
adtDeclToSortId a = do
    i <- getNextId
    return $ SortId (adtName a) (Id i)

sortIdOfVarDecl :: HasSortIds e => e -> VarDecl -> Either Error SortId
sortIdOfVarDecl e = findSortId e . varDeclSort

sortIdOfVarDeclM :: HasSortIds e => e -> VarDecl -> CompilerM SortId
sortIdOfVarDeclM e f = liftEither $ sortIdOfVarDecl e f

-- | TODO: QUESTION: do we return an error when there are variables whose types
-- couldn't be inferred, or do we leave the error occur when some other
-- function asks for the type of the variable later on?
inferTypes :: (HasSortIds e, HasVarDecls e, HasFuncIds e)
           => e -> [FuncDecl] -> CompilerM (Map (Loc VarDeclE) SortId)
inferTypes e fs = liftEither $ do
    paramsVdSid <- Map.fromList . concat <$> traverse fParamLocSorts fs
    letVdSid    <- gInferTypes (SEnv paramsVdSid) allLetVarDecls
    return $ Map.union letVdSid paramsVdSid
    where
      allLetVarDecls = concatMap letVarDeclsInFunc fs
      gInferTypes :: SEnv (Map (Loc VarDeclE) SortId)
                  -> [LetVarDecl]
                  -> Either Error (Map (Loc VarDeclE) SortId)
      gInferTypes e' vs =
          case partitionEithers (inferVarDeclType e e' <$> vs) of
              ([], rs) -> Right $ fromSEnv $ fromList rs <> e'
              (ls, []) -> Left  Error
                          { _errorType = UndefinedType
                          , _errorLoc  = NoErrorLoc -- TODO: we could generate
                                                   -- multiple errors, giving
                                                   -- all the locations in 'ls'
                          , _errorMsg  =  "Could not infer the types: " <> (T.pack . show . (fst <$>)) ls
                          }
              (ls, rs) -> gInferTypes (fromList rs <> e') (snd <$> ls)
      fParamLocSorts :: FuncDecl -> Either Error [(Loc VarDeclE, SortId)]
      fParamLocSorts fd = zip (getLoc <$> funcParams fd) <$> fParamSorts
          where
            fParamSorts :: Either Error [SortId]
            fParamSorts = traverse (findSortId e) (varDeclSort <$> funcParams fd)

letVarDeclsInFunc :: FuncDecl -> [LetVarDecl]
letVarDeclsInFunc fd = expLetVarDecls (funcBody fd)

inferVarDeclType :: (HasSortIds e, HasVarDecls e, HasFuncIds e)
                 => e
                 -> SEnv (Map (Loc VarDeclE) SortId)
                 -> LetVarDecl -> Either (Error, LetVarDecl) (Loc VarDeclE, SortId)
inferVarDeclType e vdSid vd = left (,vd) $
    case letVarDeclSortName vd of
    Just sn -> do -- If the sort is declared, we just return it.
        sId <- findSortId e sn
        return (getLoc vd, sId)
    Nothing -> do -- If the sort is not declared, we try to infer it from the expression.
        expSids <- inferExpTypes e vdSid (varDeclExp vd)
        expSid <- getUniqueElement expSids
        return (getLoc vd, expSid)

-- | Infer the type of an expression. Due to function overloading an expression
-- could have multiple types, e.g.:
--
-- > fromString("33")
--
-- Could be a TorXakis 'Int', 'String', 'Bool', or even an 'ADT'.
--
inferExpTypes :: (HasSortIds e, HasVarDecls e, HasFuncIds e)
             => e
             -> SEnv (Map (Loc VarDeclE) SortId)
             -> ExpDecl
             -> Either Error [SortId]
inferExpTypes e vdSid ex =
    case expChild ex of
    VarRef _ l ->
        -- Find the location of the variable reference
        -- If it is a variable, return the sort id of the variable declaration.
        -- If it is a function, return the sort id's of the functions.
        (fmap pure . findVarDeclSortId vdSid ||| findFuncSortIds e) =<< findVarDecl e l
    ConstLit c ->
        return $ -- The type of any is any sort known!
            maybe (allSortIds e) pure (sortIdConst c)
    LetExp vs subEx -> do
        vsSidss <- traverse (inferExpTypes e vdSid) (varDeclExp <$> vs)
        -- Here we make sure that each variable expression has a unique type.
        vsSids <- traverse getUniqueElement vsSidss
        let vdSid' = fromList (zip (getLoc <$> vs) vsSids) <> vdSid
        inferExpTypes e vdSid' subEx
    -- TODO: shouldn't if be also a function? Defined in terms of the Haskell's @if@ operator.
    If e0 e1 e2 -> do
        [se0s, se1s, se2s] <- traverse (inferExpTypes e vdSid) [e0, e1, e2]
        when (sortIdBool `notElem` se0s)
            (Left Error
                { _errorType = TypeMismatch
                , _errorLoc  = getErrorLoc e0
                , _errorMsg  = "Guard expression must be a Boolean."
                           <> " Got " <> T.pack (show se0s)
                })
        let ses = se1s `intersect` se2s
        when (null ses)
            (Left Error
                { _errorType = TypeMismatch
                , _errorLoc  = getErrorLoc ex
                , _errorMsg  = "The sort of the two IF branches don't match."
                           <> "(" <> T.pack (show se1s)
                           <>" and " <> T.pack (show se2s) <> ")"
                }
             )
        return ses
    Fappl _ l exs -> concat <$> do
        sess <- traverse (inferExpTypes e vdSid) exs
        for (sequence sess) $ \ses -> do
              fdis <- findFuncDecl e l
              let matchingFdis = determineF e fdis ses Nothing
              for matchingFdis $ \fdi -> do
                  fId  <- findFuncId e fdi
                  when (ses /= funcargs fId)
                      (Left Error
                       { _errorType = TypeMismatch
                       , _errorLoc  = getErrorLoc l
                       , _errorMsg  = "Function arguments sorts do not match "
                                     <> T.pack (show ses)
                       })
                  return $ funcsort fId

sortIdConst :: Const -> Maybe SortId
sortIdConst (BoolConst _)   = Just sortIdBool
sortIdConst (IntConst _ )   = Just sortIdInt
sortIdConst (StringConst _) = Just sortIdString
sortIdConst (RegexConst _)  = Just sortIdRegex
-- Any does not have a sort id associated with it.
--
-- Note that it seems like a bad design decision to change 'AnyConst' to
-- include the 'SortId', since the parser does not need to know anything about
-- the internal representations used by 'TorXakis'.
sortIdConst AnyConst        = Nothing

checkSortIds :: SortId -> SortId -> Either Error ()
checkSortIds sId0 sId1 =
    when (sId0 /= sId1) $ Left Error
    { _errorType = TypeMismatch
    , _errorLoc  = NoErrorLoc
    , _errorMsg  = "Sorts do not match "
                  <> T.pack (show sId0) <> T.pack (show sId1)
    }

