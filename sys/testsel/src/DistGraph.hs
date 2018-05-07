{-# LANGUAGE ViewPatterns        #-}
module DistGraph where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import qualified Data.Maybe as Maybe
import Data.Foldable as Foldable
import qualified Data.List as List

import qualified TxsDefs
import qualified BehExprDefs

import qualified SplitGraph
import SplitGraph as SplitGraph (SplitGraph)
import qualified SuspAut
import SuspAut as SuspAut (SuspAut,SuspState)
import qualified Aut
import qualified Util


buildDistGraph :: SuspAut -> SplitGraph -> Set SuspState -> Maybe TxsDefs.BExpr
buildDistGraph aut graph stateSet = buildDistGraph' aut graph stateSet TxsDefs.stop

buildDistGraph' :: SuspAut -> SplitGraph -> Set SuspState -> TxsDefs.BExpr -> Maybe TxsDefs.BExpr
buildDistGraph' aut graph stateSet dg = if (Set.size stateSet) <= 1 then Just dg
                                            else if TxsDefs.isStop dg
                                                    then case getEvFromLCA aut graph stateSet of
                                                            Nothing -> Nothing
                                                            Just lca -> buildDistGraph' aut graph stateSet lca
                                                    else case dg of
                                                           (TxsDefs.view -> BehExprDefs.ActionPref mu bexp) ->
                                                                case buildDistGraph' aut graph (Aut.afterSet stateSet (Util.actOfferToChanid mu) aut) bexp of
                                                                    Nothing -> Nothing
                                                                    Just newBexp -> Just (TxsDefs.actionPref mu newBexp)
                                                           (TxsDefs.view -> BehExprDefs.Choice bexps) ->
                                                                    case (List.foldl (\m bexp -> case buildDistGraph' aut graph stateSet bexp of
                                                                                        Nothing -> Nothing
                                                                                        Just newBexp -> Just (newBexp:Maybe.fromJust m)) (Just []) bexps) of
                                                                        Nothing -> Nothing
                                                                        Just list -> Just (TxsDefs.choice list)

getEvFromLCA :: SuspAut -> SplitGraph -> Set SuspState -> Maybe TxsDefs.BExpr
getEvFromLCA aut graph stateSet = let lcas = SplitGraph.getLCA graph stateSet
                                    in case Foldable.find (Maybe.fromJust . SplitGraph.isInjective) lcas of
                                        Nothing -> case Foldable.find (\n -> SplitGraph.injectiveSet aut stateSet (enabEvidence $ Maybe.fromJust $ SplitGraph.evidence n)) lcas of
                                                    Nothing -> Nothing
                                                    Just lca -> Just (Maybe.fromJust $ SplitGraph.evidence $ lca)
                                        Just lca -> Just $ Maybe.fromJust $ SplitGraph.evidence lca

enabEvidence :: TxsDefs.BExpr -> Set TxsDefs.ChanId
enabEvidence ev = if TxsDefs.isStop ev then Set.empty
                  else case ev of
                        (TxsDefs.view -> BehExprDefs.ActionPref mu _) -> Set.singleton $ Util.actOfferToChanid mu
                        (TxsDefs.view -> BehExprDefs.Choice bexps) -> Set.unions $ map enabEvidence bexps