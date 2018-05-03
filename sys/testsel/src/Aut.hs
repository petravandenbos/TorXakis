module Aut(Aut(..),State(..),show,after,computeCompRel,inp,out,enab,initial,states,inputs,outputs,states) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import Data.Map as Map (Map)
import qualified Data.Map as Map
import Data.Maybe as Maybe

import qualified TxsDefs

import qualified Util

data Aut a = Aut {initial :: (State a), states :: Set (State a), idStateMap :: (Map a (State a)), inputs ::  (Set TxsDefs.ChanId), outputs :: (Set TxsDefs.ChanId)}
instance (Show a) => Show (Aut a) where
    show (Aut initial states map inps outs) = "Initial: " ++ (show initial) ++ "\n" ++
                                        "States: " ++ (show states) ++ "\n" ++
                                        "Input alphabet:" ++ (show $ Set.map Util.chanToName inps) ++
                                        "Output alphabet:" ++ (show $ Set.map Util.chanToName outs)
                                        --"IdStateMap: " ++ (show $ (Map.mapKeys Util.stateToName . Map.map (Util.stateToName . sid)) map)

data State a = State {sid :: a, inp :: Set TxsDefs.ChanId, out :: Set TxsDefs.ChanId, trans :: Map TxsDefs.ChanId a}
    deriving (Eq, Ord,Show)

enab :: (State a) -> Set TxsDefs.ChanId
enab s = Set.union (inp s) (out s)

after :: Ord a => (State a) -> TxsDefs.ChanId -> (Aut a) -> Maybe (State a)
after (State _ _ _ trans) c (Aut _ _ idmap _ _) =  case (Map.lookup c trans) of
                                    Nothing -> Nothing
                                    Just s -> Map.lookup s idmap

computeCompRel :: Ord a => (Aut a) -> Set (State a,State a)
computeCompRel aut@(Aut _ states _ _ _) =
                    let first = Set.fromList [(q,q') | q <- Set.toList states,  q' <- Set.toList states] in
                        let second = expandCompRel aut first in
                            computeCompRec first second (expandCompRel aut)

computeCompRec :: Eq a => Set (State a,State a) -> Set (State a,State a) -> (Set (State a,State a) -> Set (State a,State a)) -> Set (State a,State a)
computeCompRec first second f = if first == second then first else computeCompRec second (f second) f

expandCompRel :: Ord a => (Aut a) -> Set (State a,State a) -> Set (State a,State a)
expandCompRel aut@(Aut _ states _ _ _) rel =
    Set.fromList [(q,q') | q <- Set.toList states, q' <- Set.toList states,
             let mem = (\c -> Set.member (Maybe.fromJust $ after q c aut, Maybe.fromJust $ after q' c aut)  rel),
             (all mem (Set.intersection (inp q) (inp q'))) && (any mem (Set.intersection (out q) (out q')))]

