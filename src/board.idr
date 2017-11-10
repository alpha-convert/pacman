module Board
import Graphics.SDL2 as SDL2
import System as System
import Data.Vect as Vect
import Data.Matrix as Matrix
import Data.Matrix.Numeric
import Data.Fin
import Debug.Trace

%access export

public export
{- Row vector -}
data RingVect : (len : Nat) -> (t : Type) -> Type where
  Nil : RingVect Z t
  (::) : t -> RingVect n t -> RingVect (S n) t
%name RingVect xs,ys,zs,ws

rmap : (a -> b) -> RingVect n a -> RingVect n b
rmap f [] = []
rmap f (x :: xs) = (f x) :: (rmap f xs)

Functor (RingVect n) where
  map = rmap

{- Precondition: n > 0 -}
index : (x : Nat) -> RingVect n a -> a
index x [y] = y
index Z (y :: xs) {n = (S k)} = y
index (S j) (y :: xs) {n = (S k)} = case ((S k) `isLTE` (S j)) of {- x >= n -}
                                       Yes pf => index ((S j) - (S k)) (y :: xs)
                                       No pf => index j xs

{- n = rows -}
{- m = cols -}
SphereMat : Nat -> Nat -> Type -> Type
SphereMat n m a = RingVect n (RingVect m a)
%name SphereMat m0, m1

getRow : SphereMat n m a -> Nat -> RingVect m a
getRow m0 k= index k m0

getCol : SphereMat n m a -> Nat -> RingVect n a
getCol m0 k= map (index k) m0

getEntry : SphereMat n m a -> Nat -> Nat -> a
getEntry m0 k j = index j (getRow m0 k)

matToList : SphereMat n m a -> List (Nat,Nat,a)
matToList m0 {n = Z} {m = Z} = []
matToList m0 {n = Z} {m = (S k)} = []
matToList m0 {n = (S k)} {m = Z} = []
matToList m0 {n = (S k)} {m = (S j)} = [(x,y,e) |
                    x <- [0..k],
                    y <- [0..j],
                    e <- [getEntry m0 x y]
                  ]

isTraversable : SphereMat a b Int -> (x : Nat) -> (y : Nat) -> Bool
isTraversable m0 x y = getEntry m0 y x == 1


{-The board is a sphere-}
board : SphereMat 20 20 Int
board = (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::1::1::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::1::1::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::1::1::1::1::1::1::1::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::1::0::0::0::0::0::1::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::1::0::1::1::1::0::1::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::1::0::1::1::1::0::1::0::0::0::0::0::0::[]) ::
        (1::1::1::1::1::1::1::1::0::1::1::1::0::1::1::1::1::1::1::1::[]) ::
        (0::0::0::1::0::0::0::1::0::0::1::0::0::1::0::0::1::0::0::0::[]) ::
        (0::0::0::1::0::0::0::1::1::1::1::1::1::1::0::0::1::0::0::0::[]) ::
        (0::0::0::1::0::0::0::0::0::0::1::0::0::0::0::0::1::0::0::0::[]) ::
        (0::0::0::1::0::0::0::0::0::0::1::0::0::0::0::0::1::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) :: []
        {-
        (1::1::1:: []) ::
        (1::0::1:: []) ::
        (0::1::1:: []) :: []
        -}


