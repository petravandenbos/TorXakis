module SplitGraph(buildSplitGraph,show) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map as Map (Map)
import qualified Data.Maybe as Maybe
import qualified Data.PQueue.Prio.Max as Queue
import qualified Data.List as List

import qualified TxsDefs

import qualified SuspAut
import SuspAut as SuspAut (SuspAut,SuspState)
import qualified Aut
import qualified Util

import Debug.Trace as Trace

data SplitNode = SplitNode {nodeStates :: (Set SuspState), children :: Set (Set SuspState), evidence :: Maybe TxsDefs.BExpr, isInjective :: Maybe Bool} --, splittedStates :: Maybe (Set SuspState)
    deriving (Eq,Ord)

instance Show SplitNode where
    show (SplitNode s c e i) = "node: " ++ (show $ Set.map  (Util.stateToName . Aut.sid) s) ++ "\n" ++
                               "children: " ++ (show $ Set.map (\n -> Set.map  (Util.stateToName . Aut.sid) n) c) ++ "\n" ++
                               "evidence: " ++ (case e of Nothing -> "No evidence"; Just ev -> Util.bExprToString ev)  ++ "\n" ++
                               "isInjective: " ++ (case i of Nothing -> "Unknown"; Just b -> show b)

data SplitGraph = SplitGraph {root :: (Set SuspState), nodeMap :: Map (Set SuspState) SplitNode} --, lcaMap :: Map (Set SuspState) (Set SplitNode)

instance Show SplitGraph where
    show (SplitGraph r map) = Map.foldl (\str s -> str ++ (show s) ++ "\n\n") "" map

{-data Evidence = Nil | Prefix TxsDefs.ChanId Evidence | Plus Evidence Evidence
    deriving (Eq,Ord,Show)-}

isLeaf :: SplitNode -> Bool
isLeaf (SplitNode _ c _ _) = Set.null c

isNonLeaf :: SplitNode -> Bool
isNonLeaf n = not $ isLeaf n

leaves :: SplitGraph -> Map (Set SuspState) SplitNode
leaves (SplitGraph _ n) = Map.filter (Set.null . children) n

getSplit :: Set SuspState -> SplitNode -> Set (Set SuspState)
getSplit stateSet node = Set.fromList [Set.fromList [ q | q <- Set.toList stateSet, Set.member q c ] | c <- Set.toList (children node)]

injective :: SuspAut -> Set SuspState -> TxsDefs.ChanId -> Bool
injective aut stateSet mu = let b = ((Set.member mu (Aut.outputs aut)) || (all (\s -> Set.member mu $ Aut.inp s) stateSet))
                                list = [if (Set.member mu (Set.intersection (Aut.enab q) (Aut.enab q')))
                                           then let s1 = Maybe.fromJust $ Aut.after q mu aut
                                                    s2 = Maybe.fromJust $ Aut.after q' mu aut
                                                   in s1 /= s2
                                           else True | q <- Set.toList stateSet, q' <- Set.toList stateSet, q /= q']
                            in b && (and list)

injectiveSet :: SuspAut -> Set SuspState -> (Set TxsDefs.ChanId) -> Bool
injectiveSet aut stateSet chanSet = and $ Set.map (injective aut stateSet) chanSet

-- getSplittedStates children -> splitted states
{-getSplittedStates :: Set (Set SuspState) -> Set SuspState
getSplittedStates set = Set.foldl (\sp states -> Set.foldl (\acc' s -> if Set.member s acc' then Set.delete s acc' else Set.insert s acc') sp states) Set.empty set-}

getLCA :: SplitGraph -> Set SuspState -> Set SplitNode
getLCA g@(SplitGraph r map) lcaStates = let (lca,_,_) = getLCA' g (Maybe.fromJust $ Map.lookup r map) lcaStates Map.empty in lca

-- getLCA' splitgraph needlcsforthesestates currentnode visitedsplitnodes -> foundlcas foundcandidate visitedsplitnodes
getLCA' :: SplitGraph -> SplitNode -> Set SuspState -> Map SplitNode Bool -> (Set SplitNode, Bool,Map SplitNode Bool)
getLCA' g currentNode lcaStates visited =
                            case Map.lookup currentNode visited of
                                Just b -> (Set.empty,b,visited)
                                Nothing ->
                                 if isLeaf currentNode
                                   then if any (flip Set.member lcaStates) (nodeStates currentNode) then (Set.empty, True, Map.insert currentNode True visited) else(Set.empty, False, Map.insert currentNode False visited)
                                   else let childNodes = (Set.map (\childstates -> Maybe.fromJust $ Map.lookup childstates (nodeMap g)) (children currentNode))
                                            (totalFound,totalNoLCA,totalVisited) =
                                                Set.foldl (\acc child ->
                                                 case acc of
                                                 (totalFound,totalNoLCA,totalVisited) ->
                                                    let (childFound,foundLCA,childVisited) = getLCA' g child lcaStates totalVisited
                                                          in (Set.union totalFound childFound, totalNoLCA && (not foundLCA),Map.union totalVisited childVisited)) (Set.empty,False,visited) childNodes
                                           in if totalNoLCA then (totalFound,False,Map.insert currentNode False totalVisited)
                                                else let done = isLCA currentNode lcaStates
                                                    in if done then (Set.insert currentNode totalFound,True,Map.insert currentNode True totalVisited) else (totalFound,True, Map.insert currentNode True totalVisited)

isLCA :: SplitNode -> Set SuspState -> Bool
isLCA node lcaStates = (isNonLeaf node) && (Set.isSubsetOf lcaStates (nodeStates node)) && ((Set.size $ getSplit lcaStates node) >= 2)

makeRoot :: SuspAut -> SplitGraph
makeRoot aut = SplitGraph (Aut.states aut) (Map.singleton (Aut.states aut) (SplitNode (Aut.states aut) Set.empty Nothing Nothing))

assignChildren :: SplitGraph -> SplitNode -> (Set (Set SuspState)) -> TxsDefs.BExpr -> Bool -> SplitGraph
assignChildren (SplitGraph r nodeMap) oldNode@(SplitNode states _ _ _) newChildren evidence isInjective
    = if (null $ children oldNode)
        then let newNode = SplitNode states newChildren (Just evidence) (Just isInjective)
               in (SplitGraph r (Map.insert states newNode nodeMap))
        else error ("Cannot assign child nodes to non-leaf node!")

buildSplitGraph :: SuspAut -> SplitGraph
buildSplitGraph aut = let g = makeRoot aut
                          queue = Queue.singleton (Set.size $ root g) (Maybe.fromJust $ Map.lookup (root g) (nodeMap g))
                      in buildSplitGraph' aut g queue Set.empty

buildSplitGraph' :: SuspAut -> SplitGraph -> Queue.MaxPQueue Int SplitNode -> Set SplitNode -> SplitGraph
buildSplitGraph' aut graph todoQ notSplit = case Queue.maxView todoQ of
                                        Nothing -> if Set.null notSplit then graph else buildSplitGraph' aut graph (Set.foldl (\accQueue node -> Queue.insert (Set.size $ nodeStates node) node accQueue) (Queue.empty) notSplit) Set.empty
                                        Just (node, newQ) -> case splitNode aut graph node of
                                                                    Nothing -> buildSplitGraph' aut graph newQ (Set.insert node notSplit)
                                                                    Just newGraph -> buildSplitGraph' aut newGraph newQ notSplit

condition1 :: SuspAut -> SplitNode -> Bool
condition1 aut (SplitNode nodeStates _ _ _) = all (\x -> any (\q -> Set.notMember x (Aut.out q)) nodeStates) (Aut.outputs aut)

splitCondition1 :: SuspAut -> SplitGraph -> SplitNode -> SplitGraph
splitCondition1 aut graph node = let outputs = Set.toList (Aut.outSet (nodeStates node))
                                     children = Set.fromList [Set.fromList [ q | q <- Set.toList (nodeStates node), Set.member x (Aut.out q) ] | x <- outputs]
                                     evidence = TxsDefs.choice [ TxsDefs.actionPref (Util.chanIdToActOffer x) TxsDefs.stop | x <- outputs]
                                     inj = injectiveSet aut (nodeStates node) (Set.fromList outputs)
                                   in assignChildren graph node children evidence inj

splitNode :: SuspAut -> SplitGraph -> SplitNode -> Maybe SplitGraph
splitNode aut graph node = if condition1 aut node then Just (splitCondition1 aut graph node) else Just graph
{-

splitOnTransition :: SuspAut -> SplitGraph -> SplitNode -> Maybe SplitGraph
splitOnTransition aut graph node = -}
