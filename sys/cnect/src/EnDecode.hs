{-
TorXakis - Model Based Testing
Copyright (c) 2015-2016 TNO and Radboud University
See license.txt
-}


-- ----------------------------------------------------------------------------------------- --

module EnDecode

-- ----------------------------------------------------------------------------------------- --
--
-- En- and Decoding between abstract model actions and
-- concrete representations of actions on connections
--  
-- ----------------------------------------------------------------------------------------- --
-- export

( encode    -- encode :: Action -> IOC SAction
            -- mapping from Abstract to Representation
, decode    -- decode :: SAction -> IOC Action
            -- mapping from Representation to Abstract
)

-- ----------------------------------------------------------------------------------------- --
-- import

where

-- import System.IO
import Control.Monad.State
-- import Debug.Trace
-- 
-- import qualified Data.Char as Char
-- import qualified Data.List as List
import qualified Data.Set  as Set
import qualified Data.Map  as Map

import CoreUtils

-- import from serverenv
import qualified EnvServer  as IOS

-- import from core
import qualified TxsCore  as TxsCore
import qualified EnvCore  as IOC
-- import qualified Eval  as Eval

--import from defs
import TxsDefs
import TxsDDefs
import TxsUtils
import TxsShow


-- ----------------------------------------------------------------------------------------- --
-- encode :  encoding from Abstract to Concrete (String)


encode :: IOS.EnvS -> Action -> IOC.IOC SAction

encode envs (Act offs)  =  do
     ( _, _, towhdls ) <- return $ IOS.tow envs
     ss                <- return $ [ tow
                                   | tow@(ConnHtoW chan h vars vexp) <- towhdls 
                                   , Set.singleton chan == Set.map fst offs
                                   ]
     ConnHtoW chan h vars vexp <- return $ 
                             case ss of
                             { [ tow ] -> tow
                             ; _       -> error $ "Encode: No (unique) action\n" ++ (fshow ss)
                             }
     walues <- return $ case Set.toList offs of
                        { [ ( chanid, wals ) ] -> wals
                        ; _                    -> error $ "Encode: No (unique) action\n"
                        }
     wenv     <- return $ Map.fromList $ zip vars walues
     sval     <- TxsCore.txsEval $ cstrEnv (Map.map cstrConst wenv) vexp
     return $ case sval of
              { Cstring s -> SAct h s
              ; _         -> error "Encode: No encoding to String\n"
              }

encode envs (ActQui)  =  do
     return $ SActQui


-- ----------------------------------------------------------------------------------------- --
-- decode :  decoding from Concrete (String) to Abstract


decode :: IOS.EnvS -> SAction -> IOC.IOC Action 

decode envs (SAct hdl sval)  =  do
     let ( _, _, frowhdls )         = IOS.frow envs
         ConnHfroW chan h var vexps = case [ frow
                                           | frow@(ConnHfroW _ h _ _) <- frowhdls
                                           , h == hdl
                                           ] of
                                      { [ frow ] -> frow
                                      ; _        -> error $ "TXS Decode: No (unique) handle\n"
                                      }
      in do senv     <- return $ Map.fromList $ [ (var, cstrConst (Cstring sval)) ]
            wals     <- mapM (TxsCore.txsEval . (cstrEnv senv)) vexps
            return $ Act ( Set.singleton (chan,wals) )

decode envs (SActQui)  =  do
     return $ ActQui


-- ----------------------------------------------------------------------------------------- --
--                                                                                           --
-- ----------------------------------------------------------------------------------------- --
