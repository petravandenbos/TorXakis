{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
module SuspAut(SuspAut,SuspState,stautToSusp,tupleStateSetToString,show) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import Data.Map as Map (Map)
import qualified Data.Map as Map

import qualified TxsDefs

import qualified Util
import qualified Aut

type SuspAut = Aut.Aut TxsDefs.StatId

type SuspState = Aut.State TxsDefs.StatId

instance Show SuspState where
    show (Aut.State s inps outs t) = show (Util.stateToName s,
                                   map Util.chanToName (Set.toList inps),
                                   map Util.chanToName (Set.toList outs),
                                   map (\t -> (Util.chanToName $ fst t, Util.stateToName $ snd t)) (Map.toList t))

tupleStateSetToString :: Set (SuspState,SuspState) -> String
tupleStateSetToString set = show $ Set.map (\t -> (Util.stateToName $ Aut.sid $ fst t, Util.stateToName $ Aut.sid $ snd t)) set

-- TODO checken dat StautDef non-blocking is

stautToSusp :: TxsDefs.StatId -> [TxsDefs.Trans] -> Set TxsDefs.ChanId -> Set TxsDefs.ChanId -> SuspAut
stautToSusp initial transs inps outs = let statemap = stautToStateMap transs inps outs in
                                        case Map.lookup initial statemap of
                                            Nothing -> error ("Initial state does not have any transitions")
                                            Just (ini,outi,tmapi) ->
                                                let statesandmap = getStatesAndMap statemap
                                                in Aut.Aut (Aut.State initial ini outi tmapi) (fst statesandmap) (snd statesandmap) inps outs

getStatesAndMap :: Map TxsDefs.StatId (Set TxsDefs.ChanId, Set TxsDefs.ChanId, Map TxsDefs.ChanId TxsDefs.StatId) -> (Set SuspState, Map TxsDefs.StatId SuspState)
getStatesAndMap statemap = (Map.foldlWithKey (\setandmap key val -> case val of
                                                                       (ins,outs,tmaps) ->
                                                                           let state = (Aut.State key ins outs tmaps) in
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