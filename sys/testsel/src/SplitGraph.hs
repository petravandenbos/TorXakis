module SplitGraph(makeRoot,leaves) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map as Map (Map)
import qualified SuspAut as SuspAut
import SuspAut as SuspAut (SuspAut,State)
import qualified Data.Maybe as Maybe

import qualified TxsDefs


data SplitNode = SplitNode {node :: (Set State), children :: Set (Set State), splittedStates :: Maybe (Set State), evidence :: Maybe Evidence}
    deriving (Eq,Ord,Show)

data SplitGraph = SplitGraph {root :: SplitNode, nodeMap :: Map (Set State) SplitNode, lcaMap :: Map (Set State) (Set SplitNode)}
    deriving (Show)

data Evidence = Nil | Prefix TxsDefs.ChanId Evidence | Plus Evidence Evidence
    deriving (Eq,Ord,Show)

makeRoot :: Set State -> SplitGraph
makeRoot set = let root = SplitNode set Set.empty Nothing Nothing in SplitGraph root (Map.singleton set root) Map.empty

assignChildren :: SplitGraph -> SplitNode -> (Set (Set State)) -> Evidence -> SplitGraph
assignChildren (SplitGraph r nodeMap lcaMap) oldNode@(SplitNode states _ _ _) newChildren newEvidence
    = if (null $ children oldNode)
        then let splitted = getSplittedStates newChildren
                 newNode = (SplitNode states newChildren (Just splitted) (Just newEvidence))
                    in (SplitGraph r
                                   (Map.insert states newNode nodeMap)
                                   (Map.insertWith (Set.union) splitted (Set.singleton newNode) lcaMap) )
        else error ("Cannot assign child nodes to non-leaf node!")

leaves :: SplitGraph -> Map (Set State) SplitNode
leaves (SplitGraph _ n _) = Map.filter (Set.null . children) n

inducedSplit :: SuspAut.SuspAut -> SplitNode -> TxsDefs.ChanId -> SplitNode -> Set (Set State)
inducedSplit aut l c v = Set.fromList [Set.fromList [ q | q <- Set.toList (node l), mu <- Set.toList (SuspAut.enab q), Set.member (Maybe.fromJust $ SuspAut.after q mu aut) c ] | c <- Set.toList (children v)]

condition1 :: SuspAut -> SplitNode -> Bool
condition1 aut (SplitNode states _ _ _) = all (\x -> any (\q -> Set.notMember x (SuspAut.out q)) states) (SuspAut.outputs aut)

-- getSplittedStates children -> splitted states
getSplittedStates :: Set (Set State) -> Set State
getSplittedStates set = Set.foldl (\sp states -> Set.foldl (\acc' s -> if Set.member s acc' then Set.delete s acc' else Set.insert s acc') sp states) Set.empty set