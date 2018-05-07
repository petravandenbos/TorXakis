module Aut(Aut(..),State(..),show,after,computeCompRel,inp,out,enab,initial,states,inputs,outputs,states, outSet,afterSet) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import Data.Map as Map (Map)
import qualified Data.Map as Map
import Data.Maybe as Maybe

import qualified TxsDefs

import qualified Util

import Debug.Trace as Trace

data Aut a b = Aut {initial :: (State a b), states :: Set (State a b), idStateMap :: (Map a (State a b)), inputs ::  (Set b), outputs :: (Set b)}
instance (Show a, Show b) => Show (Aut a b) where
    show (Aut initial states map inps outs) = "Initial: " ++ (show initial) ++ "\n" ++
                                        "States: " ++ (show states) ++ "\n" ++
                                        "Input alphabet:" ++ (show $ inps) ++
                                        "Output alphabet:" ++ (show $ outs)
                                        --"IdStateMap: " ++ (show $ (Map.mapKeys Util.stateToName . Map.map (Util.stateToName . sid)) map)

data State a b = State {sid :: a, inp :: Set b, out :: Set b, trans :: Map b a}
    deriving (Ord,Show)

instance (Eq a) => Eq (State a b) where
    (==) s1 s2 = (sid s1) == (sid s2)
    (/=) s1 s2 = (sid s1) /= (sid s2)

enab :: Ord b => (State a b) -> Set b
enab s = Set.union (inp s) (out s)

outSet :: Ord b => Set (State a b) -> Set b
outSet set = Set.foldl (\chans state -> Set.union chans (out state)) Set.empty set

after :: (Ord a, Ord b) => (State a b) -> b -> (Aut a b) -> Maybe (State a b)
after state mu aut =  case (Map.lookup mu (trans state)) of
                                    Nothing -> Nothing
                                    Just s -> Map.lookup s (idStateMap aut)

afterSet :: (Ord a, Ord b) => Set (State a b) -> b -> (Aut a b) -> Set (State a b)
afterSet stateSet mu aut = Set.foldl (\set s -> case after s mu aut of Nothing -> set; Just s' -> Set.insert s' set) Set.empty stateSet

computeCompRel :: (Ord a, Ord b) => Aut a b -> Set (State a b,State a b)
computeCompRel aut = let first = Set.fromList [(q,q') | q <- Set.toList (states aut),  q' <- Set.toList (states aut)]
                         second = expandCompRel aut first in
                            computeCompRec first second (expandCompRel aut)

computeCompRec :: (Eq a, Eq b) => Set (State a b,State a b) -> Set (State a b,State a b) -> (Set (State a b,State a b) -> Set (State a b,State a b)) -> Set (State a b,State a b)
computeCompRec first second f = if first == second then first else computeCompRec second (f second) f

expandCompRel :: (Ord a, Ord b) => (Aut a b) -> Set (State a b,State a b) -> Set (State a b,State a b)
expandCompRel aut@(Aut _ states _ _ _) rel =
    Set.fromList [(q,q') | q <- Set.toList states, q' <- Set.toList states,
             let mem = (\c -> Set.member (Maybe.fromJust $ after q c aut, Maybe.fromJust $ after q' c aut)  rel),
             (all mem (Set.intersection (inp q) (inp q'))) && (any mem (Set.intersection (out q) (out q')))]

