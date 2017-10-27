module Main
import Graphics.SDL2 as SDL2
import System as System
import Data.Vect as Vect
import Data.Matrix as Matrix
import Data.Matrix.Numeric
import Data.Fin

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

getRow : Nat -> SphereMat n m a -> RingVect m a
getRow k m0 = index k m0

getCol : Nat -> SphereMat n m a -> RingVect n a
getCol k m0 = map (index k) m0

getEntry : Nat -> Nat -> SphereMat n m a -> a
getEntry k j m0 = index j (getRow k m0)

{-The board is a sphere-}
board : SphereMat 4 3 Int
board = (1 :: 0 :: 0 :: []) ::
        (1 :: 1 :: 1 :: []) ::
        (1 :: 0 :: 1 :: []) ::
        (0 :: 1 :: 1 :: []) :: []


isTraversable : SphereMat a b Int -> Bool


drawRect : (x : Int) -> (y : Int) -> (w : Int) -> (h : Int) -> Int -> Int -> Int -> Renderer -> IO ()
drawRect x y w h r g b = \ren => SDL2.filledRect ren x y w h r g b 255


fail : (msg: String) -> IO ()
fail msg = do
  err <- getError
  fPutStr stderr $ msg ++ " failed:" ++ err
  fflush stderr
  System.exit 1

width : Int
width = 540

height : Int
height = 960

squareSize : Int
squareSize = 50

main : IO ()
main = (do
  renderer <- SDL2.init width height
  loop renderer
  SDL2.destroyRenderer renderer
  quit)
    where
      loop : Renderer -> IO ()
      loop renderer = do
        False <- SDL2.pollEventsForQuit | pure ()
        True <- SDL2.setRendererDrawColor renderer 0 0 111 255
          | fail "setRendererDrawColor"
        SDL2.renderClear renderer
        (drawRect ((width `div` 2) - (squareSize `div` 2))
                                  ((height `div` 2) - (squareSize `div` 2))
                                  squareSize  squareSize  255  0  0) renderer
        SDL2.renderPresent renderer
        loop renderer
