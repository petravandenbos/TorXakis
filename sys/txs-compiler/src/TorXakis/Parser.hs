module TorXakis.Parser
    ( ParsedDefs
    , adts
    , fdefs
    , txsP
    , parseFile
    , parse
    )
where

import qualified Data.Text as T
import           Text.Parsec ( (<|>), many, eof, runParserT )
import           Control.Arrow (left)
import           Control.Monad.Identity (runIdentity)
    
import           TorXakis.Compiler.Error (Error)
import           TorXakis.Parser.Data
import           TorXakis.Parser.FuncDefs (fdeclP)
import           TorXakis.Parser.TypeDefs (adtP)
import           TorXakis.Parser.Common (TxsParser)

parse :: String -> Either Error ParsedDefs
parse = undefined

parseFile :: FilePath -> IO (Either Error ParsedDefs)
parseFile fp =  left (T.pack . show) <$> do
    input <- readFile fp
    return $ runIdentity (runParserT txsP (mkState 1000) fp input)
    
-- | TorXakis definitions generated by the parser.
data ParsedDefs = ParsedDefs
    { adts  :: [ADTDecl]
    , fdefs :: [FuncDecl]
    } deriving (Eq, Show)

-- | TorXakis top-level definitions
data TLDef = TLADT ADTDecl
           | TLFun FuncDecl

-- | Group a list of top-level definitions per-type.
asParsedDefs :: [TLDef] -> ParsedDefs
asParsedDefs ts = ParsedDefs as fs
    where (as, fs) = foldr sep ([], []) ts
          sep  (TLADT a) (xs, ys) = (a:xs, ys)
          sep  (TLFun f) (xs, ys) = (xs, f:ys)

-- | Root parser for the TorXakis language.
txsP :: TxsParser ParsedDefs
txsP = do
    ts <- many $  fmap TLADT adtP
              <|> fmap TLFun fdeclP
    eof
    return $ asParsedDefs ts
