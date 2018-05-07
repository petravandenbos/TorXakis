{-# LANGUAGE ViewPatterns        #-}
module Util where

import qualified TxsDefs
import           Name
import qualified Data.Set as Set
import qualified Data.List as List
import qualified BehExprDefs
import qualified ValExpr
import qualified ConstDefs

stateToName :: TxsDefs.StatId -> Name
stateToName (TxsDefs.StatId n _ _) = n

chanToName :: TxsDefs.ChanId -> Name
chanToName (TxsDefs.ChanId n _ _) = n

getChanSet :: [Set.Set TxsDefs.ChanId] -> Set.Set TxsDefs.ChanId
getChanSet [] = Set.empty
getChanSet (set:rest) = if (Set.size set == 1) then Set.insert (Set.elemAt 0 set) (getChanSet rest) else error  ("no single chan: " ++ (show set))

actOfferToChanid :: TxsDefs.ActOffer -> TxsDefs.ChanId
actOfferToChanid (BehExprDefs.ActOffer ofs _ _) = if (Set.size ofs) == 1 then case (Set.elemAt 0 ofs) of (BehExprDefs.Offer chan _) -> chan else error ("no single chan: " ++ (show ofs))

chanIdToActOffer :: TxsDefs.ChanId -> TxsDefs.ActOffer
chanIdToActOffer chanId = TxsDefs.ActOffer (Set.singleton (TxsDefs.Offer chanId [])) Set.empty (ValExpr.cstrConst $ ConstDefs.Cbool True)

actOfferToString :: TxsDefs.ActOffer -> String
actOfferToString act = show $ chanToName $ actOfferToChanid act

bExprToString :: TxsDefs.BExpr -> String
bExprToString (TxsDefs.view -> BehExprDefs.ActionPref act bexp) = if TxsDefs.isStop bexp then (actOfferToString act) ++ ".Nil" else (actOfferToString act) ++ ".(" ++ bExprToString bexp ++ ")"
bExprToString (TxsDefs.view -> BehExprDefs.Choice bexps) = List.intercalate " + " (map bExprToString bexps)
bExprToString _ = "No evidence-BExpr!"

addTo2Tup :: (a,b) -> c -> (a,b,c)
addTo2Tup (a,b) c = (a,b,c)