{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}

-- ----------------------------------------------------------------------------------------- --
{-# LANGUAGE OverloadedStrings #-}
module NComp

-- ----------------------------------------------------------------------------------------- --
--
-- Test selection by N-Complete algorithm for ioco
--
-- ----------------------------------------------------------------------------------------- --
-- export

( nComplete   -- :: TxsDefs.ProcDef -> IOC.IOC TxsDefs.PurpDef
)

-- ----------------------------------------------------------------------------------------- --
-- import

where

import qualified Data.List   as List
import           Data.Monoid
import Data.Set as Set (Set)
import qualified Data.Set as Set
import Data.Map as Set (Map)
import qualified Data.Map as Map

import qualified Data.Text           as T

import qualified SplitGraph
import qualified SuspAut
import qualified Aut
import qualified Util


import qualified EnvCore     as IOC

import qualified ConstDefs
import qualified StdTDefs
import qualified TxsDefs
import qualified ValExpr
import qualified EnvData

-- ----------------------------------------------------------------------------------------- --
-- nComplete

nComplete :: [Set TxsDefs.ChanId] -> [Set TxsDefs.ChanId] ->
             TxsDefs.StatId -> [TxsDefs.Trans] ->
             IOC.IOC (Maybe TxsDefs.PurpDef)

nComplete insyncs outsyncs initial transs = do
          IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR (
              let aut = SuspAut.stautToSusp initial transs (Util.getChanSet insyncs) (Util.getChanSet outsyncs) in
                show $ SplitGraph.makeRoot aut
                ) ]

          --  "compatible: " ++ SuspAut.tupleStateSetToString (Aut.computeCompRel aut)
          -- SplitGraph.makeRoot $ Set.fromList [1,2,3]
          -- map stateToName $ getStatesFromTransList transs []
          return Nothing



{-nComplete insyncs outsyncs
          ini@(TxsDefs.StatId nm uid (TxsDefs.ProcId nm' uid' _ _ _)) transs =
     let splsyncs = [ Set.singleton StdTDefs.chanIdQstep
                    , Set.singleton StdTDefs.chanIdHit
                    , Set.singleton StdTDefs.chanIdMiss
                    ]
         gids     = [ TxsDefs.GoalId ("Goal_" <> nm <> nm' <> (T.pack . show) n ) (uid*uid'+n) | n <- [1..] ]
         goals    = [ (gid,bexp) | (gid,bexp) <- zip gids (allPaths ini transs) ]
      in return $ Just $ TxsDefs.PurpDef insyncs outsyncs splsyncs goals-}

{-allPaths :: TxsDefs.StatId -> [TxsDefs.Trans] -> [TxsDefs.BExpr]
allPaths ini transs = [ path2bexpr p
                         | p@(TxsDefs.Trans from _a _u _to : _pp) <- List.permutations transs
                         , isPath p
                         , from == ini
                         ]

isPath :: [TxsDefs.Trans] -> Bool
isPath []                 = True
isPath [TxsDefs.Trans {}] = True
isPath (TxsDefs.Trans _from _a _u to : TxsDefs.Trans from' a' u' to' : pp) =
    to == from' && isPath (TxsDefs.Trans from' a' u' to' : pp)

path2bexpr :: [TxsDefs.Trans] -> TxsDefs.BExpr
path2bexpr [] = TxsDefs.actionPref
                    (TxsDefs.ActOffer (Set.singleton $ TxsDefs.Offer StdTDefs.chanIdHit []) Set.empty (ValExpr.cstrConst (ConstDefs.Cbool True)))
                    TxsDefs.stop
path2bexpr (TxsDefs.Trans _from a _u _to : pp) = TxsDefs.actionPref a (path2bexpr pp)-}

-- ----------------------------------------------------------------------------------------- --
--                                                                                           --
-- ----------------------------------------------------------------------------------------- --
