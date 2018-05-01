module SplitGraph(makeRoot,leaves) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map as Map (Map)
import qualified SuspAut as SuspAut
import qualified Data.Maybe as Maybe

import qualified TxsDefs


data SplitNode = SplitNode {node :: (Set SuspAut.State), children :: Set SplitNode}
    deriving (Eq,Ord,Show)

data SplitGraph = SplitGraph {root :: SplitNode, nodes :: Set SplitNode, evidence :: Map SplitNode String}
    deriving (Show)

makeRoot :: Set SuspAut.State -> SplitGraph
makeRoot set = let root = SplitNode set Set.empty in SplitGraph root (Set.singleton root) Map.empty

leaves :: SplitGraph -> Set SplitNode
leaves (SplitGraph _ n _) = Set.filter (Set.null . children) n

inducedSplit :: SuspAut.SuspAut -> SplitNode -> TxsDefs.ChanId -> SplitNode -> Set (Set SuspAut.State)
inducedSplit aut l c v = Set.fromList [Set.fromList [ q | q <- Set.toList (node l), mu <- Set.toList (SuspAut.enab q), Set.member (Maybe.fromJust $ SuspAut.after q mu aut) (node c) ] | c <- Set.toList (children v)]