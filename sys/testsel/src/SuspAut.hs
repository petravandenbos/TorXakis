module SuspAut(SuspAut,State,show,stautToSusp,after,computeCompRel,inp,out,enab,tupleStateSetToString,initial,states,inputs,outputs) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import Data.Map as Map (Map)
import qualified Data.Map as Map
import Data.Maybe as Maybe
import Data.List as List
import Data.Function as Function
import Debug.Trace

import qualified TxsDefs

import qualified Util as Util

data SuspAut = SuspAut {initial :: State, states :: (Set State), idStateMap :: (Map TxsDefs.StatId State), inputs ::  (Set TxsDefs.ChanId), outputs :: (Set TxsDefs.ChanId)}
instance Show SuspAut where
    show (SuspAut initial states map inps outs) = "Initial: " ++ (show initial) ++ "\n" ++
                                        "States: " ++ (show states) ++ "\n" ++
                                        "Input alphabet:" ++ (show $ Set.map Util.chanToName inps) ++
                                        "Output alphabet:" ++ (show $ Set.map Util.chanToName outs)
                                        --"IdStateMap: " ++ (show $ (Map.mapKeys Util.stateToName . Map.map (Util.stateToName . sid)) map)

data State = State {sid :: TxsDefs.StatId, inp :: Set TxsDefs.ChanId, out :: Set TxsDefs.ChanId, trans :: Map TxsDefs.ChanId TxsDefs.StatId}
    deriving (Eq, Ord)

instance Show State where
    show (State s inps outs t) = show (Util.stateToName s,
                                   map Util.chanToName (Set.toList inps),
                                   map Util.chanToName (Set.toList outs),
                                   map (\t -> (Util.chanToName $ fst t, Util.stateToName $ snd t)) (Map.toList t))

tupleStateSetToString :: Set (State,State) -> String
tupleStateSetToString set = show $ Set.map (\t -> (Util.stateToName $ sid $ fst t, Util.stateToName $ sid $ snd t)) set

stautToSusp :: TxsDefs.StatId -> [TxsDefs.Trans] -> Set TxsDefs.ChanId -> Set TxsDefs.ChanId -> SuspAut
stautToSusp initial transs inps outs = let statemap = stautToStateMap transs inps outs in
                                        case Map.lookup initial statemap of
                                            Nothing -> error ("Initial state does not have any transitions")
                                            Just (ini,outi,tmapi) ->
                                                let statesandmap = getStatesAndMap statemap
                                                in SuspAut (State initial ini outi tmapi) (fst statesandmap) (snd statesandmap) inps outs

getStatesAndMap :: Map TxsDefs.StatId (Set TxsDefs.ChanId, Set TxsDefs.ChanId, Map TxsDefs.ChanId TxsDefs.StatId) -> (Set State, Map TxsDefs.StatId State)
getStatesAndMap statemap = (Map.foldlWithKey (\setandmap key val -> case val of
                                                                       (ins,outs,tmaps) ->
                                                                           let state = (State key ins outs tmaps) in
                                                                            (Set.insert state (fst setandmap), Map.insert key state (snd setandmap))) (Set.empty,Map.empty) statemap)

stautToStateMap :: [TxsDefs.Trans] -> Set TxsDefs.ChanId -> Set TxsDefs.ChanId -> Map TxsDefs.StatId (Set TxsDefs.ChanId, Set TxsDefs.ChanId, Map TxsDefs.ChanId TxsDefs.StatId)
stautToStateMap transs inps outs = foldl (\m (TxsDefs.Trans f l _ t) -> -- map: statid -> (inp,out,Map(sym,statid))
                                       let chan = (Util.actOfferToChanid l)
                                          in
                                       if (Set.member chan inps) then Map.insertWith mergeMaps f (Set.singleton chan, Set.empty,Map.singleton chan t) m
                                       else if (Set.member chan outs) then Map.insertWith mergeMaps f (Set.empty,Set.singleton chan,Map.singleton chan t) m
                                       else error ("Channel " ++ (show $ (Util.chanToName . Util.actOfferToChanid) l) ++ " neither input nor output!")
                                       ) Map.empty transs


mergeMaps :: (Set TxsDefs.ChanId, Set TxsDefs.ChanId, Map TxsDefs.ChanId TxsDefs.StatId) -> (Set TxsDefs.ChanId, Set TxsDefs.ChanId, Map TxsDefs.ChanId TxsDefs.StatId) -> (Set TxsDefs.ChanId, Set TxsDefs.ChanId, Map TxsDefs.ChanId TxsDefs.StatId)
mergeMaps (ni,no,nm) (oi,oo,om) =
    let (c,s) = head $ Map.toList nm in
    case (Map.lookup c om) of
        Nothing -> (Set.union ni oi, Set.union no oo,Map.insert c s om)
        Just _ -> error "stautdef nondeterministic!"

enab :: State -> Set TxsDefs.ChanId
enab s = Set.union (inp s) (out s)

after :: State -> TxsDefs.ChanId -> SuspAut -> Maybe State
after (State _ _ _ trans) c (SuspAut _ _ idmap _ _) =  case (Map.lookup c trans) of
                                    Nothing -> Nothing
                                    Just s -> Map.lookup s idmap

computeCompRel :: SuspAut -> Set (State,State)
computeCompRel aut@(SuspAut _ states _ _ _) =
                    let first = Set.fromList [(q,q') | q <- Set.toList states,  q' <- Set.toList states] in
                        let second = expandCompRel aut first in
                            computeCompRec first second (expandCompRel aut)

computeCompRec :: Set (State,State) -> Set (State,State) -> (Set (State,State) -> Set (State,State)) -> Set (State,State)
computeCompRec first second f = if first == second then first else computeCompRec second (f second) f

expandCompRel :: SuspAut -> Set (State,State) -> Set (State,State)
expandCompRel aut@(SuspAut _ states _ _ _) rel =
    Set.fromList [(q,q') | q <- Set.toList states, q' <- Set.toList states,
             let mem = (\c -> Set.member (Maybe.fromJust $ after q c aut, Maybe.fromJust $ after q' c aut)  rel),
             (all mem (Set.intersection (inp q) (inp q'))) && (any mem (Set.intersection (out q) (out q')))]

