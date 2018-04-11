module TorXakis.CompilerSpec where

import           GHC.Stack
import           Data.Either          (isRight)
import           Data.Foldable        (traverse_)
import qualified Data.Map             as Map
import           Data.Set             (Set)
import qualified Data.Set             as Set
import           System.FilePath      ((</>))
import           System.FilePath.Find (extension, find, (==?))
import           Test.Hspec           (Expectation, Spec, describe, it,
                                       parallel, runIO, shouldBe, shouldSatisfy)

import           FuncTable            (Signature, toMap)
import           Id                   (Id, Resettable, reset)
import           Sigs                 (Sigs, func, sort, pro, chan)
import           TxsAlex              (txsLexer)
import           TxsDefs              (TxsDefs, cstrDefs, funcDefs, sortDefs,
                                       varDefs, procDefs, chanDefs, statDefs,
                                       modelDefs, mapperDefs, cnectDefs,
                                       goalDefs, purpDefs)

import           TxsHappy             (txsParser)
import           VarId                (VarId)

import           TorXakis.Compiler    (compileFile)

spec :: Spec
spec = do
    describe "Correctly compiles the incremental (WIP)" $ do
        fs <- runIO $ find (return True) (extension ==? ".txs")
              ("test" </> "data" </> "success")
        parallel $ traverse_ compareWithCurrent fs
    describe "Compiles the examples in `examps` folder (WIP)" $ do
        fs <- runIO $ find (return True) (extension ==? ".txs")
              ("test" </> "data" </> "examps")
        parallel $ traverse_ testCompiler fs
    where
        testCompiler fp = it (show fp) $ do
            r <- compileFile fp
            r `shouldSatisfy` isRight
        compareWithCurrent fp = it (show fp) $ do
            r <- compileFile fp
            -- First sanity check, the models are successfully compiled.
            r `shouldSatisfy` isRight
            let Right (_, tdefs, sigs) = r
            (_, tdefs', sigs') <- txsCompile fp
            -- Check that the 'TxsDef's generated by the `front` coincide with
            -- those generated by `txs-compiler`
            sortDefs    tdefs ~==~ sortDefs    tdefs'
            cstrDefs    tdefs ~==~ cstrDefs    tdefs'
            funcDefs    tdefs ~==~ funcDefs    tdefs'
            procDefs    tdefs ~==~ procDefs    tdefs'
            chanDefs    tdefs ~==~ chanDefs    tdefs'
            varDefs     tdefs ~==~ varDefs     tdefs'
            statDefs    tdefs ~==~ statDefs    tdefs'
            modelDefs   tdefs ~==~ modelDefs   tdefs'
            purpDefs    tdefs ~==~ purpDefs    tdefs'
            goalDefs    tdefs ~==~ goalDefs    tdefs'
            mapperDefs  tdefs ~==~ mapperDefs  tdefs'
            cnectDefs   tdefs ~==~ cnectDefs   tdefs'
            -- Check that the `Sigs` generated by `front` coincide with those
            -- generated by `txs-compiler`. We cannot test the handlers for
            -- equality, since they are functions.
            Set.fromList (chan sigs) ~==~ Set.fromList (chan sigs')
            signatures sigs          ~==~ signatures sigs'
            Set.fromList (pro sigs)  ~==~ Set.fromList (pro sigs')
            sort       sigs          ~==~ sort       sigs'
            (Map.keys . toMap . func) sigs `shouldBe` (Map.keys . toMap . func) sigs'
                where
                  signatures :: Sigs VarId -> Set Signature
                  signatures = Set.fromList . concat . (Map.keys <$>) . Map.elems . toMap . func

-- | Equality modulo unique id's.
(~==~) :: (HasCallStack, Resettable e, Show e, Eq e) => e -> e -> Expectation
e0 ~==~ e1 = reset e0 `shouldBe` reset e1

txsCompile :: FilePath -> IO (Id, TxsDefs, Sigs VarId)
txsCompile = (txsParser . txsLexer <$>) . readFile
