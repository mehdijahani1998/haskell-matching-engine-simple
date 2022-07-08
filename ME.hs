{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module ME where
import Text.Printf
import Control.Exception
import Test.QuickCheck
import Data.Ord (comparing)
import Data.List (sortBy, sortOn)

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


-- HERE GOES GENERATORS -- 

instance Arbitrary OrderBook where
    arbitrary = genOrderBook

instance Arbitrary Order where
    arbitrary = genRandomOrder

type MinimumQuantity = Maybe Quantity

genMinQty :: Gen MinimumQuantity
genMinQty = elements list
    where list = Nothing : [Just n | n<-[0..1000]]

genQtyandMinQty :: Gen (Quantity, MinimumQuantity)
genQtyandMinQty = elements list
    where list = [(a, Nothing) | a <- [1..1000]] ++ [(a, Just b) | a <- [1..1000], b <- [1..1000], a >= b]


genOnlyBuySide :: Gen Side
genOnlyBuySide = elements [Buy]

genOnlySellSide :: Gen Side
genOnlySellSide = elements [Sell]

genBothSides :: Gen Side
genBothSides = elements [Buy, Sell]

genIDs :: Gen OrderID
genIDs = elements list
    where list = [oid | oid <- [1..10]]

genPrice :: Gen Price
genPrice = elements list
    where list = [a | a <- [1..1000]]

genOnlyBuyOrder :: Gen Order
genOnlyBuyOrder = do oid <- genIDs
                     price <- genPrice
                     buySide <- genOnlyBuySide
                     (quantity , minQty) <- genQtyandMinQty
                     return (LimitOrder oid price quantity buySide minQty)

genOnlySellOrder :: Gen Order
genOnlySellOrder = do oid <- genIDs
                      price <- genPrice
                      sellSide <- genOnlySellSide
                      (quantity , minQty) <- genQtyandMinQty
                      return (LimitOrder oid price quantity sellSide minQty)

genRandomOrder :: Gen Order
genRandomOrder = do oid <- genIDs
                    price <- genPrice
                    side <- genBothSides
                    (quantity , minQty) <- genQtyandMinQty
                    return (LimitOrder oid price quantity side minQty)

genBuyQueue :: Gen OrderQueue
genBuyQueue = listOf genOnlyBuyOrder `suchThat` isBuyQueueSorted

genSellQueue :: Gen OrderQueue
genSellQueue = listOf genOnlySellOrder `suchThat` isSellQueueSorted

genOrderBook :: Gen OrderBook
genOrderBook = do buyQ <- genBuyQueue
                  sellQ <- genSellQueue
                  return (OrderBook buyQ sellQ)

getOrderPrice :: Order -> Price
getOrderPrice = price

sortOrderQueue :: [Order] -> [Order]
sortOrderQueue = sortOn getOrderPrice

isSellQueueSorted :: OrderQueue -> Bool
isSellQueueSorted sellQ = sellQ == sortOrderQueue sellQ

isBuyQueueSorted :: OrderQueue -> Bool
isBuyQueueSorted buyQ = buyQ == reverse (sortOrderQueue buyQ)

prop_isOrderBookSorted :: OrderBook -> Bool
prop_isOrderBookSorted ob = isSellQueueSorted (sellQueue  ob) && isBuyQueueSorted (buyQueue ob)


instance Arbitrary Trade where

    arbitrary = do
        Positive priceTraded <- arbitrary
        Positive quantityTraded <- arbitrary
        Positive buyId <- arbitrary
        Positive sellId <- arbitrary
        return $ Trade priceTraded quantityTraded buyId sellId

-- Conservation of quantity property --

-- 1. Auxiliary functions
getTradesQuantitySum :: [Trade] -> Int
getTradesQuantitySum [] = 0
getTradesQuantitySum [t] = quantityTraded t
getTradesQuantitySum (t:ts) = quantityTraded t + getTradesQuantitySum ts

getOrderQueueQuantitySum :: OrderQueue -> Int
getOrderQueueQuantitySum [] = 0
getOrderQueueQuantitySum [order] = quantity order
getOrderQueueQuantitySum (ord:ob) = quantity ord + getOrderQueueQuantitySum ob

getOrderBookQuantitySum :: OrderBook -> Int
getOrderBookQuantitySum ob = getOrderQueueQuantitySum (buyQueue ob) + getOrderQueueQuantitySum (sellQueue ob)

orderBookNotNull :: OrderBook -> Bool
orderBookNotNull ob = not (null (sellQueue ob) || null (buyQueue ob))

onlyOneTrade :: [Trade] -> Bool
onlyOneTrade trd = length trd <= 1

-- 2. Property check functions
quantitySumEquityCheck :: Order -> OrderBook -> Bool
quantitySumEquityCheck newOrder orderBook = quantity newOrder + getOrderBookQuantitySum orderBook == getOrderBookQuantitySum remainOrderBook + 2 * getTradesQuantitySum trades
    where (remainOrderBook, trades) = matchNewOrder newOrder orderBook

prop_quantitySumEqual :: Order -> OrderBook -> Property
prop_quantitySumEqual newOrder orderBook = orderBookNotNull orderBook ==> quantitySumEquityCheck newOrder orderBook

prop_quantitySumEqual_Classified:: Order -> OrderBook -> Property
prop_quantitySumEqual_Classified newOrder orderBook = collect (length trades) $ quantitySumEquityCheck newOrder orderBook
    where (remainOrderBook, trades) = matchNewOrder newOrder orderBook


-- Heads of sell queue and buy queue can be matched or not property --

-- 1. Auxiliary functions
ordersCantBeMatched :: Order -> Order -> Bool
ordersCantBeMatched bord sord
    | side bord == side sord = True
    | price bord < price sord = True
    | otherwise = False

canHeadsMatchAfter :: Order -> OrderBook -> Bool
canHeadsMatchAfter newOrder orderBook = orderBookNotNull remainOrderBook
                                        && ordersCantBeMatched buyHead sellHead
                                        || null (buyQueue remainOrderBook)
                                        || null (sellQueue remainOrderBook)
    where (remainOrderBook, trades) = matchNewOrder newOrder orderBook
          buyHead = head $ buyQueue remainOrderBook
          sellHead = head $ sellQueue remainOrderBook

canHeadsMatchBefore :: OrderBook -> Bool
canHeadsMatchBefore orderBook = ordersCantBeMatched buyHead sellHead
    where buyHead = head $ buyQueue orderBook
          sellHead = head $ sellQueue orderBook

-- 2. Property check function
prop_canHeadsMatch :: Order -> OrderBook -> Property
prop_canHeadsMatch newOrder orderBook = orderBookNotNull orderBook &&  canHeadsMatchBefore orderBook ==> canHeadsMatchAfter newOrder orderBook


-- Compare trades price with sell and buy queue --

tradePriceMoreThanBuyLessThanSell :: Order -> OrderBook -> Bool
tradePriceMoreThanBuyLessThanSell newOrder orderBook = if side newOrder == Buy then headTradePrice <= sellHeadPrice else headTradePrice >= buyHeadPrice
    where (remainOrderBook, trades) = matchNewOrder newOrder orderBook
          nullTradePrice = if side newOrder == Buy then 0 else 1000
          headTradePrice = if null trades then nullTradePrice else priceTraded (last trades)
          buyHeadPrice = if null $ buyQueue remainOrderBook then 0 else price (head $ buyQueue remainOrderBook)
          sellHeadPrice = if null $ sellQueue remainOrderBook then 1000 else price (head $ sellQueue remainOrderBook)

prop_tradePriceCompareWithHeads_mbls :: Order -> OrderBook -> Property
prop_tradePriceCompareWithHeads_mbls newOrder orderBook = orderBookNotNull orderBook &&
                                                      orderBookNotNull remainOrderBook &&
                                                      not (null trades)
                                                      ==> tradePriceMoreThanBuyLessThanSell newOrder orderBook
    where (remainOrderBook, trades) = matchNewOrder newOrder orderBook

prop_tradePriceCompareWithHeads_simple_mbls :: Order -> OrderBook -> Bool
prop_tradePriceCompareWithHeads_simple_mbls newOrder orderBook = tradePriceMoreThanBuyLessThanSell newOrder orderBook
    where (remainOrderBook, trades) = matchNewOrder newOrder orderBook














