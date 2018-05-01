module Util where

import qualified TxsDefs
import           Name
import qualified Data.Set as Set
import qualified BehExprDefs

stateToName :: TxsDefs.StatId -> Name
stateToName (TxsDefs.StatId n _ _) = n

chanToName :: TxsDefs.ChanId -> Name
chanToName (TxsDefs.ChanId n _ _) = n

getChanSet :: [Set.Set TxsDefs.ChanId] -> Set.Set TxsDefs.ChanId
getChanSet [] = Set.empty
getChanSet (set:rest) = if (Set.size set == 1) then Set.insert (Set.elemAt 0 set) (getChanSet rest) else error  ("no single chan: " ++ (show set))

actOfferToChanid :: BehExprDefs.ActOffer -> TxsDefs.ChanId
actOfferToChanid (BehExprDefs.ActOffer ofs _ _) = if (Set.size ofs) == 1 then case (Set.elemAt 0 ofs) of (BehExprDefs.Offer chan _) -> chan else error ("no single chan: " ++ (show ofs))