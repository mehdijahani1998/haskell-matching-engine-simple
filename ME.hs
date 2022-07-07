module ME where
import Text.Printf
import Control.Exception

type Quantity = Int
type Price = Int
type TimeStamp = Int
type OrderID = Int

data Side = Buy | Sell deriving (Show, Eq, Ord)

data Order = LimitOrder 
  { oid :: OrderID
  , price :: Price
  , quantity :: Quantity
  , side :: Side
  , minQty :: Maybe Quantity
  } | IcebergOrder 
  { oid :: OrderID
  , price :: Price
  , quantity :: Quantity
  , side :: Side
  , minQty :: Maybe Quantity
  , disclosedQty :: Quantity
  , peakSize :: Quantity
  } deriving (Show, Eq)

limitOrder i p q s m =
  assert (i >= 0) $
  assert (p > 0) $
  assert (q > 0) $
  case m of {(Just mq) -> assert (mq > 0); otherwise -> id} $
  LimitOrder i p q s m

icebergOrder i p q s m dq ps =
  assert (i >= 0) $
  assert (p > 0) $
  assert (q >= 0) $
  case m of {(Just mq) -> assert (mq > 0); otherwise -> id} $
  assert (dq <= q) $
  assert (ps > 0) $
  IcebergOrder i p q s m dq ps

type OrderQueue = [Order]

data OrderBook = OrderBook {
    buyQueue :: OrderQueue
  , sellQueue :: OrderQueue
  } deriving (Show, Eq)

data Trade = Trade {
    priceTraded :: Price
  , quantityTraded :: Quantity
  , buyId :: OrderID
  , sellId :: OrderID
  } deriving (Show, Eq)

decQty :: Order -> Quantity -> Order
decQty (LimitOrder i p q s mq) q' = limitOrder i p (q - q') s mq
decQty (IcebergOrder i p q s mq dq ps) q' = icebergOrder i p (q - q') s mq (dq -q') ps

queuesBefore :: Order -> Order -> Bool
queuesBefore o o'
  | (side o == Sell) && (side o' == Sell) = (price o < price o')
  | (side o == Buy) && (side o' == Buy) = (price o > price o')
  | otherwise = error "incomparable orders"

enqueueOrder :: Order -> OrderQueue -> OrderQueue
enqueueOrder (IcebergOrder i p q s mq dq ps) =
  enqueueOrder' (IcebergOrder i p q s mq (min q ps) ps)
enqueueOrder (LimitOrder i p q s mq) =
  enqueueOrder' (LimitOrder i p q s mq)

enqueueOrder' :: Order -> OrderQueue -> OrderQueue
enqueueOrder' o [] = [o]
enqueueOrder' o (o1:os)
  | queuesBefore o o1 = o:(o1:os)
  | otherwise = o1:(enqueueOrder' o os)

enqueue :: Order -> OrderBook -> OrderBook
enqueue o ob
  | side o == Buy = OrderBook (enqueueOrder o $ buyQueue ob) (sellQueue ob)
  | side o == Sell = OrderBook (buyQueue ob) (enqueueOrder o $ sellQueue ob) 

enqueueIcebergRemainder :: OrderQueue -> Order -> OrderQueue
enqueueIcebergRemainder os (IcebergOrder _ _ 0 _ _ _ _) = os
-- enqueueIcebergRemainder os (IcebergOrder i p q s mq 0 ps) =
--   enqueueOrder (icebergOrder i p q s mq (min q ps) ps) os
enqueueIcebergRemainder os (IcebergOrder i p q s mq 0 ps)
  | q <= ps = enqueueOrder (icebergOrder i p q s mq q ps) os
  | otherwise = enqueueOrder (icebergOrder i p q s mq ps ps) os

matchBuy :: Order -> OrderQueue -> (Maybe Order, OrderQueue, [Trade])
matchBuy o [] = (Just o, [], [])
matchBuy o oq@((LimitOrder i1 p1 q1 s1 mq1):os)
  | p < p1 = (Just o, oq, [])
  | q < q1 = (Nothing, (decQty (head oq) q):os, [Trade p1 q i i1])
  | q == q1 = (Nothing, os, [Trade p1 q i i1])
  | q > q1 = let
      (o', ob', ts') = matchBuy (decQty o q1) os
      in
        (o', ob', (Trade p1 q1 i i1):ts')
  where
    p = price o
    q = quantity o
    i = oid o

matchBuy o ((IcebergOrder i1 p1 q1 s1 mq1 dq1 ps1):os)
  | p < p1 = (Just o, (icebergOrder i1 p1 q1 s1 mq1 dq1 ps1):os, [])
  | q < dq1 = (Nothing, (icebergOrder i1 p1 (q1-q) s1 mq1 (dq1-q) ps1):os, [Trade p1 q i i1])
  | q == dq1 = let
      newQueue = enqueueIcebergRemainder os (icebergOrder i1 p1 (q1-dq1) s1 mq1 0 ps1)
      in
        (Nothing, newQueue, [Trade p1 q i i1])
  | q > dq1 = let
      newQueue = enqueueIcebergRemainder os (icebergOrder i1 p1 (q1-dq1) s1 mq1 0 ps1)
      (o', ob', ts') = matchBuy (decQty o dq1) newQueue
      in
        (o', ob', (Trade p1 dq1 i i1):ts')
  where
    p = price o
    q = quantity o
    i = oid o

matchSell :: Order -> OrderQueue -> (Maybe Order, OrderQueue, [Trade])
matchSell o [] = (Just o, [], [])

matchSell o oq@((LimitOrder i1 p1 q1 s1 mq1):os)
  | p > p1 = (Just o, oq, [])
  | q < q1 = (Nothing, (decQty (head oq) q):os, [Trade p1 q i1 i])
  | q == q1 = (Nothing, os, [Trade p1 q i1 i])
  | q > q1 = let
      (o', ob', ts') = matchSell (decQty o q1) os
      in
        (o', ob', (Trade p1 q1 i1 i):ts')
  where
    p = price o
    q = quantity o
    i = oid o

matchSell o ((IcebergOrder i1 p1 q1 s1 mq1 dq1 ps1):os)
  | p > p1 = (Just o, (icebergOrder i1 p1 q1 s1 mq1 dq1 ps1):os, [])
  | q < dq1 = (Nothing, (icebergOrder i1 p1 (q1-q) s1 mq1 (dq1-q) ps1):os, [Trade p1 q i1 i])
  | q == dq1 = let
      newQueue = enqueueIcebergRemainder os (icebergOrder i1 p1 (q1-dq1) s1 mq1 0 ps1)
      in
        (Nothing, newQueue, [Trade p1 q i1 i])
  | q > dq1 = let
      newQueue = enqueueIcebergRemainder os (icebergOrder i1 p1 (q1-dq1) s1 mq1 0 ps1)
      (o', ob', ts') = matchSell (decQty o dq1) newQueue
      in
        (o', ob', (Trade p1 dq1 i1 i):ts')
  where
    p = price o
    q = quantity o
    i = oid o

matchNewOrder :: Order -> OrderBook -> (OrderBook, [Trade])
matchNewOrder o ob
  | side o == Buy = let
      (rem, sq, ts) = (matchBuy o (sellQueue ob))
      in
        case rem of
          Nothing -> (OrderBook (buyQueue ob) sq, ts)
          Just o' -> (enqueue o' $ OrderBook (buyQueue ob) sq, ts)
  | side o == Sell = let
      (rem, bq, ts) = (matchSell o (buyQueue ob))
      in
        case rem of
          Nothing -> (OrderBook bq (sellQueue ob), ts)
          Just o' -> (enqueue o' $ OrderBook bq (sellQueue ob), ts)

handleNewOrder :: Order -> OrderBook -> (OrderBook, [Trade])
handleNewOrder o ob = let
  (ob', ts') = matchNewOrder o ob
  in
    case minQty o of
      Nothing -> (ob', ts')
      Just mq -> 
        if (sum $ map quantityTraded ts') >= mq then
          (ob', ts')
        else
          (ob, [])
