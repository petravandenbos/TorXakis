{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE ScopedTypeVariables        #-}
module SplitGraph(buildSplitGraph,show) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map as Map (Map)
import qualified Data.Maybe as Maybe
import qualified Data.PQueue.Prio.Max as Queue
import qualified Data.List as List
import Data.Foldable as Foldable

import qualified TxsDefs
import qualified BehExprDefs

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

isUnsplittable :: Set SuspState -> Set (SuspState,SuspState) -> Bool
isUnsplittable stateSet compRel = Set.isSubsetOf (Set.fromList [(q,q') | q <- Set.toList stateSet, q' <- Set.toList stateSet]) compRel

isLeaf :: SplitNode -> Bool
isLeaf node = Set.null $ children node

isNonLeaf :: SplitNode -> Bool
isNonLeaf n = not $ isLeaf n

getInducedSplit :: SuspAut -> Set SuspState -> TxsDefs.ChanId -> SplitNode -> Set (Set SuspState)
getInducedSplit aut stateSet mu node = let ind = (Set.fromList [Set.fromList [ q | q <- Set.toList stateSet,
                                                                                    case Aut.after q mu aut of
                                                                                        Nothing -> False
                                                                                        (Just s) -> Set.member s c ] | c <- Set.toList (children node)])
                                        in -- Trace.trace ("indsplit: " ++ (show $ Set.map (Util.stateToName . Aut.sid) (nodeStates node))
                                           -- ++ (show $ Util.chanToName mu) ++
                                           -- " :: " ++ (show $ Set.map (Set.map (Util.stateToName . Aut.sid)) ind))
                                            (Set.delete Set.empty ind)

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
getLCA g@(SplitGraph r map) lcaStates = let (lca,_,_) = getLCA' g (Maybe.fromMaybe (error "getLCA") $ Map.lookup r map) lcaStates Map.empty in lca

-- getLCA' splitgraph needlcsforthesestates currentnode visitedsplitnodes -> foundlcas foundcandidate visitedsplitnodes
getLCA' :: SplitGraph -> SplitNode -> Set SuspState -> Map SplitNode Bool -> (Set SplitNode, Bool,Map SplitNode Bool)
getLCA' g currentNode lcaStates visited =
                            case Map.lookup currentNode visited of
                                Just b -> (Set.empty,b,visited)
                                Nothing ->
                                 if isLeaf currentNode
                                   then if any (flip Set.member lcaStates) (nodeStates currentNode) then (Set.empty, True, Map.insert currentNode True visited) else(Set.empty, False, Map.insert currentNode False visited)
                                   else let childNodes = (Set.map (\childstates -> Maybe.fromMaybe (error "getLCA'") $ Map.lookup childstates (nodeMap g)) (children currentNode))
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
isLCA node lcaStates = (isNonLeaf node)
                        && (Set.isSubsetOf lcaStates (nodeStates node))
                        && any (\t -> all (\ch -> Set.notMember (fst t) ch || Set.notMember (snd t) ch) (children node))
                                [(q,q') | q <- Set.toList lcaStates, q' <- Set.toList lcaStates,q /= q']

makeRoot :: SuspAut -> SplitGraph
makeRoot aut = SplitGraph (Aut.states aut) (Map.singleton (Aut.states aut) (SplitNode (Aut.states aut) Set.empty Nothing Nothing))

assignChildren :: SplitGraph -> SplitNode -> (Set (Set SuspState)) -> TxsDefs.BExpr -> Bool -> SplitGraph
assignChildren (SplitGraph r nodeMap) oldNode@(SplitNode states _ _ _) newChildren evidence isInjective
    = if (isLeaf oldNode)
        then let newNode = SplitNode states newChildren (Just evidence) (Just isInjective)
                 childNodes = Set.map (\ch -> SplitNode ch Set.empty Nothing Nothing) newChildren
                 newNodeMap = Map.insert states newNode (Set.foldl (\map ch -> Map.insert (nodeStates ch) ch map) nodeMap childNodes)
               in -- Trace.trace ("added children: " ++ (show $ Set.map (Set.map (Util.stateToName . Aut.sid)) newChildren))
                    (SplitGraph r newNodeMap)
        else error ("Cannot assign child nodes to non-leaf node!")

buildSplitGraph :: SuspAut -> SplitGraph
buildSplitGraph aut = let g = makeRoot aut
                          queue = Queue.singleton (Set.size $ root g) (Maybe.fromMaybe (error "build graph") $ Map.lookup (root g) (nodeMap g))
                          compRel = Aut.computeCompRel aut
                      in buildSplitGraph' aut g queue Set.empty compRel

buildSplitGraph' :: SuspAut -> SplitGraph -> Queue.MaxPQueue Int SplitNode -> Set SplitNode -> Set (SuspState,SuspState) -> SplitGraph
buildSplitGraph' aut graph todoQ notSplit compRel = case Queue.maxView todoQ of
                                        Nothing -> if Set.null notSplit then graph else buildSplitGraph' aut graph (Set.foldl (\accQueue node -> Queue.insert (Set.size $ nodeStates node) node accQueue) (Queue.empty) notSplit) Set.empty compRel
                                        Just (node, newQ) -> case splitNode aut graph node compRel of
                                                                    Nothing -> buildSplitGraph' aut graph newQ (Set.insert node notSplit) compRel
                                                                    Just newGraph -> Trace.trace ("splitted node " ++ (show $ Set.map (Util.stateToName . Aut.sid) (nodeStates node)) ++ " in " ++ (show $ Set.map (Set.map (Util.stateToName . Aut.sid)) (children (Maybe.fromJust $ Map.lookup (nodeStates node) (nodeMap newGraph)))))
                                                                                        (buildSplitGraph' aut newGraph
                                                                                            (Set.foldl (\qu ch -> if isUnsplittable ch compRel then qu
                                                                                                                    else Queue.insert (Set.size ch) (Maybe.fromJust $ Map.lookup ch (nodeMap newGraph)) qu)
                                                                                                                            newQ (children $ Maybe.fromJust $ Map.lookup (nodeStates node) (nodeMap newGraph)))
                                                                                            notSplit compRel)

condition1 :: SuspAut -> SplitNode -> Bool
condition1 aut (SplitNode nodeStates _ _ _) = all (\x -> any (\q -> Set.notMember x (Aut.out q)) nodeStates) (Aut.outputs aut)

splitCondition1 :: SuspAut -> SplitGraph -> SplitNode -> SplitGraph
splitCondition1 aut graph node = let outputs = Set.toList (Aut.outSet (nodeStates node))
                                     children = Set.fromList [Set.fromList [ q | q <- Set.toList (nodeStates node), Set.member x (Aut.out q) ] | x <- outputs]
                                     evidence = TxsDefs.choice [ TxsDefs.actionPref (Util.chanIdToActOffer x) TxsDefs.stop | x <- outputs]
                                     inj = injectiveSet aut (nodeStates node) (Set.fromList outputs)
                                   in assignChildren graph node children evidence inj

splitNode :: SuspAut -> SplitGraph -> SplitNode -> Set (SuspState,SuspState) -> Maybe SplitGraph
splitNode aut graph node compRel =
    if Set.size compRel == (Set.size $ nodeStates node) * (Set.size $ nodeStates node) then Just graph
        else if condition1 aut node then Just (splitCondition1 aut graph node)
                else splitOnTransition aut graph node compRel

splitOutputFirst :: Bool
splitOutputFirst = True

splitOnTransition :: SuspAut -> SplitGraph -> SplitNode -> Set (SuspState,SuspState) -> Maybe SplitGraph
splitOnTransition aut graph node compRel = let outputSplit = getSplitOnOutputTransition aut graph node compRel
                                               inputSplit = getSplitOnInputTransition aut graph node
                                             in case (outputSplit,inputSplit) of
                                                    (Nothing,Nothing) -> Nothing
                                                    (Nothing,Just (ci,ei,ii)) -> Just (assignChildren graph node ci ei ii)
                                                    (Just (co,eo,io),Nothing) -> Just (assignChildren graph node co eo io)
                                                    (Just (co,eo,io),Just (ci,ei,ii)) -> if (splitOutputFirst && io) || (not(ii) && io) || (not(ii) && splitOutputFirst)
                                                                                        then Just (assignChildren graph node co eo io)
                                                                                        else Just (assignChildren graph node ci ei ii)

condition2 :: SuspAut -> SplitGraph -> SplitNode -> Set (SuspState,SuspState) -> Maybe (Map TxsDefs.ChanId (Set SplitNode))
condition2 aut graph node compRel = let (bools,map) = getSymbolSplitNodeMap aut graph node (Aut.outSet (nodeStates node))
                                                (\x -> let enabledStates = Set.filter (\s -> Set.member x (Aut.out s)) (nodeStates node)
                                                        in Set.isSubsetOf (Set.fromList [(p,p') | p <- Set.toList enabledStates, p' <- Set.toList enabledStates]) compRel)
                                       in if and bools then Just map else Nothing

getSymbolSplitNodeMap :: SuspAut -> SplitGraph -> SplitNode -> Set TxsDefs.ChanId -> (TxsDefs.ChanId -> Bool) -> ([Bool], Map TxsDefs.ChanId (Set SplitNode))
getSymbolSplitNodeMap aut graph node symbols isTrivial =
    Set.foldl (\res mu -> if isTrivial mu then (True:(fst res), Map.insert mu Set.empty (snd res))
                           else let lcaNodes = getLCA graph $ Aut.afterSet (nodeStates node) mu aut
                                  in if Set.null lcaNodes then (False:(fst res), Map.empty)
                                        else (True:(fst res), Map.insert mu lcaNodes (snd res))) ([],Map.empty) symbols

getInjSplitNodeMap :: SuspAut -> Map TxsDefs.ChanId (Set SplitNode) -> Map TxsDefs.ChanId (Bool,SplitNode)
getInjSplitNodeMap aut spMap = Map.foldlWithKey
                                    (\boolinjmap k (v::Set SplitNode) -> case Foldable.find (\node -> injectiveSet aut (nodeStates node) (Aut.outSet (nodeStates node))) v of
                                                                                Nothing -> Map.insert k (False, Set.elemAt 0 v) boolinjmap
                                                                                Just injNode -> Map.insert k (True,injNode) boolinjmap) (Map.empty) spMap

                                    --                           Just children evidence isInjective | Nothing=no split
getSplitOnOutputTransition :: SuspAut -> SplitGraph -> SplitNode -> Set (SuspState,SuspState) -> Maybe ((Set (Set SuspState)), TxsDefs.BExpr, Bool)
getSplitOnOutputTransition aut graph node compRel =
    case condition2 aut graph node compRel :: Maybe (Map TxsDefs.ChanId (Set SplitNode)) of
     Nothing -> Nothing
     Just spMap -> Just (Map.foldlWithKey (\tup mu boolSplitNode ->
                                                case tup of
                                                    (children, ev, inj) ->
                                                        let (xChildren,xEvidence) = getChildEvInjForBoolSplitNode aut node mu (snd boolSplitNode)
                                                            xInj = (fst boolSplitNode)
                                                          in (Set.union children xChildren,
                                                             (if TxsDefs.isStop ev then xEvidence
                                                                else case ev of
                                                                        (TxsDefs.view -> BehExprDefs.Choice bexps) -> TxsDefs.choice (xEvidence:bexps)
                                                                        (TxsDefs.view -> BehExprDefs.ActionPref _ _) -> TxsDefs.choice [xEvidence,ev]),
                                                             inj && xInj))
                                                            (Set.empty,TxsDefs.stop,True) (getInjSplitNodeMap aut spMap))

condition3 :: SuspAut -> SplitGraph -> SplitNode -> Maybe (Map TxsDefs.ChanId (Set SplitNode))
condition3 aut graph node = let (bools,map) = getSymbolSplitNodeMap aut graph node (Set.filter (\a -> all (\q -> Set.member a (Aut.inp q)) (nodeStates node)) (Aut.inputs aut)) (const False)
                              in if or bools then Just map else Nothing

getChildEvInjForBoolSplitNode :: SuspAut -> SplitNode -> TxsDefs.ChanId -> SplitNode -> ((Set (Set SuspState)), TxsDefs.BExpr)
getChildEvInjForBoolSplitNode aut node mu splitNode = (getInducedSplit aut (nodeStates node) mu splitNode,
                                                             TxsDefs.actionPref (Util.chanIdToActOffer mu) (Maybe.fromMaybe (error "evidence") (evidence splitNode)))

getSplitOnInputTransition :: SuspAut -> SplitGraph -> SplitNode -> Maybe ((Set (Set SuspState)), TxsDefs.BExpr, Bool)
getSplitOnInputTransition aut graph node =
    case condition3 aut graph node of
        Nothing -> Nothing
        Just spMap -> case Foldable.find (fst . snd) (Map.toList $ getInjSplitNodeMap aut spMap) of
                        Nothing -> let (a,splitNodes) = Maybe.fromMaybe (error "split on input transition") (Foldable.find (not . Set.null . snd) (Map.toList spMap))
                                        in Just (Util.addTo2Tup (getChildEvInjForBoolSplitNode aut node a (Set.elemAt 0 splitNodes)) False)
                        Just (a,(_,splitNode)) -> Just (Util.addTo2Tup (getChildEvInjForBoolSplitNode aut node a splitNode) True)
