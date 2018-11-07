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

copy :: Stream Int -> Stream Int
copy (x : a : xs) = replicate x a ++ copy xs

--------------------------------------------------------------------------------

(~=) :: Eq a => Stream a -> Stream a -> [Bool]
xs ~= ys = zipWith (==) xs ys

--------------------------------------------------------------------------------

data Prop = [Bool] :==> [Bool] deriving ( Eq, Ord, Show )

injective f (xs :: Stream Bool) ys =
  f xs ~= f ys :==> xs ~= ys

prop_Test prop h (Positive n) (InfiniteList xs _) (InfiniteList ys _) =
  and (take (h n) pre) ==>
    and (take n post)
 where
  pre :==> post = prop xs ys

h1 k = k+1
h2 k = 2*k
h3 k = (k `div` 2) + 1
h4 k = k `div` 2

prop_Good_h prop h
  (Positive n, Positive k) (InfiniteList xs _) (InfiniteList ys _) =
  and (take (h n) pre) && k > h n ==>
    and (take k pre')
 where
  pre  :==> _ = prop xs ys
  pre' :==> _ = prop (cut xs) (cut ys)

  cut zs = take n zs ++ repeat False

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

