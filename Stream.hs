{-# LANGUAGE ScopedTypeVariables #-}
import Test.QuickCheck
import Test.QuickCheck.Poly( A(..) )
import Data.Maybe( isJust )

infix  0 :==>
infix  4 ~=

--------------------------------------------------------------------------------

type Stream a = [a] -- infinite list

half, twice, shift :: Stream a -> Stream a
half  (x : _ : xs) = x : half xs
twice (x : xs)     = x : x : twice xs
shift (_ : xs)     = xs

copy :: Stream (Positive Int) -> Stream (Positive Int)
copy (x : a : xs) = replicate (getPositive x) a ++ copy xs

--------------------------------------------------------------------------------

-- returns the infinite list of comparisons of each individual pair of elements
(~=) :: Eq a => Stream a -> Stream a -> [Bool]
xs ~= ys = zipWith (==) xs ys

--------------------------------------------------------------------------------

-- a datatype to represent properties of the shape
--   (t1 ~= t2) ==> (t3 ~= t4)
data Prop = [Bool] :==> [Bool] deriving ( Eq, Ord, Show )

injective f xs ys =
  f xs ~= f ys :==> xs ~= ys

--------------------------------------------------------------------------------

-- the actual property we want to test:
-- - if there is no counterexample, then everything is fine
-- - if there is a counterexample, it may be a false counterexample because
--   h may be bad

prop_Test prop h (Positive n) (InfiniteList xs _) (InfiniteList ys _) =
  and (take (h n) pre) ==>
    and (take n post)
 where
  pre :==> post = prop xs (ys :: [Bool])

h1 k = k+1
h2 k = 2*k
h3 k = (k `div` 2) + 1
h4 k = k `div` 2

--------------------------------------------------------------------------------

-- testing whether or not h is bad for the given property

prop_Good_h prop h
  (Positive n, Positive k) (InfiniteList xs _) (InfiniteList ys _) =
  and (take (h n) pre) && k > h n ==>
    and (take k pre')
 where
  pre  :==> _ = prop xs (ys :: [Bool])
  pre' :==> _ = prop (cut xs) (cut ys)

  cut zs = take n zs ++ repeat False

--------------------------------------------------------------------------------

-- some examples

main :: IO ()
main =
  do putStrLn "=== testing half with h3 ==="
     putStrLn "--- Property (should FAIL): "
     quickCheck' $ expectFailure $ prop_Test (injective half) h3
     putStrLn "--- Good h (should SUCCEED): "
     quickCheck' $ prop_Good_h (injective half) h3
     
     putStrLn "=== testing half with h4 ==="
     putStrLn "--- Property (should FAIL): "
     quickCheck' $ expectFailure $ prop_Test (injective half) h4
     putStrLn "--- Good h (should FAIL): "
     quickCheck' $ expectFailure $ prop_Good_h (injective half) h4
     
     putStrLn "=== testing twice with h2 ==="
     putStrLn "--- Property (should SUCCEED): "
     quickCheck' $ prop_Test (injective twice) h2
     putStrLn "--- Good h (should SUCCEED): "
     quickCheck' $ prop_Good_h (injective twice) h2
     
     putStrLn "=== testing twice with h1 ==="
     putStrLn "--- Property (should FAIL): "
     quickCheck' $ expectFailure $ prop_Test (injective twice) h1
     putStrLn "--- Good h (should FAIL): "
     quickCheck' $ expectFailure $ prop_Good_h (injective twice) h1
     
quickCheck' p = quickCheckWith stdArgs{ maxSuccess = 1000 } p

--------------------------------------------------------------------------------

prop_Test_Copy (Positive n) (InfiniteList xs _) (InfiniteList ys _) =
  and (take (h xs ys n) pre) ==>
    and (take n post)
 where
  pre :==> post = injective copy xs ys

  h xs ys n = calc (take n xs) `max` calc (take n ys)
  
  calc (n:xs) = getPositive n + calc (drop 1 xs)
  calc []     = 0

--------------------------------------------------------------------------------

-- testing whether or not h is bad for the given property

prop_Good_h_Copy
  (Positive n, Positive k) (InfiniteList xs _) (InfiniteList ys _) =
  and (take (h xs ys n) pre) ==>
    and (take (h xs ys n + k) pre')
 where
  pre  :==> _ = injective copy xs ys
  pre' :==> _ = injective copy (cut xs) (cut ys)

  cut zs = take n zs ++ repeat (Positive 1)

  h xs ys n = calc (take n xs) `max` calc (take n ys)
  
  calc (n:xs) = getPositive n + calc (drop 1 xs)
  calc []     = 0

prop_Bad_h_Copy
  (Positive n, Positive k) (InfiniteList xs _) (InfiniteList ys _) =
  and (take (h xs ys n) pre) ==>
    and (take (h xs ys n + k) pre')
 where
  pre  :==> _ = injective copy xs ys
  pre' :==> _ = injective copy (cut xs) (cut ys)

  cut zs = take n zs ++ repeat (Positive 1)

  h xs ys n = calc (take n xs) -- `max` calc (take n ys)
  
  calc (n:xs) = getPositive n + calc (drop 1 xs)
  calc []     = 0

--------------------------------------------------------------------------------

