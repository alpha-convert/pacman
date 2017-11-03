module Main
import Graphics.SDL2 as SDL2
import System as System
import Data.Vect as Vect
import Data.Matrix as Matrix
import Data.Matrix.Numeric
import Data.Fin
import Debug.Trace


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

{-The board is a sphere-}
board : SphereMat 20 20 Int
board = (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
        (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::[]) ::
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

matToList : SphereMat n m a -> List (Nat,Nat,a)
matToList m0 {n = Z} {m = Z} = []
matToList m0 {n = Z} {m = (S k)} = []
matToList m0 {n = (S k)} {m = Z} = []
matToList m0 {n = (S k)} {m = (S j)} = [(x,y,e) |
                    x <- [0..k],
                    y <- [0..j],
                    e <- [getEntry m0 x y]
                  ]

isTraversable : SphereMat a b Int -> Nat -> Nat -> Bool
isTraversable m0 k j = getEntry m0 k j == 1

drawCircle : (x : Int) -> (y : Int) -> (r : Int) -> Int -> Int -> Int -> Renderer -> IO ()
drawCircle x y rad r g b ren = SDL2.filledEllipse ren x y rad rad r g b 255

drawRect : (x : Int) -> (y : Int) -> (w : Int) -> (h : Int) -> Int -> Int -> Int -> Renderer -> IO ()
drawRect x y w h r g b ren = SDL2.filledRect ren y x w h r g b 255

drawSquare : (m : Nat) -> (n : Nat) -> (bw : Int) -> (bh : Int) -> (ren : Renderer) -> (Nat, Nat, Int) -> IO ()
drawSquare m n bw bh ren (x,y,isWall) = let
  blockX : Int = (cast x) * bw
  blockY : Int = (cast y) * bh
in do
  drawRect blockX blockY bw bh (255*isWall) 0 0 ren


drawBoard : SphereMat n m Int -> (w : Int) -> (h : Int) -> Renderer -> List (IO ())
drawBoard m0 w h {n} {m} = \ren => let
  widthPerBlock : Int = w `div` (cast m)
  heightPerBlock : Int = h `div` (cast n)
in
  map (drawSquare m n widthPerBlock heightPerBlock ren) (matToList m0)

data Direction = Up | Down | Left | Right
%name Direction dir,dir0

{- Player x y-}
data Player = Play Int Int
%name Player p,p'

movePlayer : Direction -> Player -> Player
movePlayer Up (Play x y) = Play x (y - 1)
movePlayer Down (Play x y) = Play x (y + 1)
movePlayer Left (Play x y) = Play (x - 1) y
movePlayer Right (Play x y) = Play (x + 1) y


{-drawCircle : (x : Int) -> (y : Int) -> (r : Int) -> Int -> Int -> Int -> Renderer -> IO ()-}

drawPlayer : Player -> SphereMat n m Int -> (w : Int) -> (h : Int) -> Renderer -> IO ()
drawPlayer (Play x y) m0 w h ren {n = n} {m = m} = if not (isTraversable m0 (cast x) (cast y))
                                                      then pure ()
                                                      else let
                                                        bw : Int = w `div` (cast m)
                                                        bh : Int = h `div` (cast n)
                                                        cx : Int = (x `mod` (cast m))*bw + (bw `div` 2)
                                                        cy : Int = (y `mod` (cast n))*bh + (bh `div` 2)
                                                        r : Int = (min bw bh) `div` 3
                                                        in
                                                        drawCircle cx cy r 0 255 0 ren



fail : (msg: String) -> IO ()
fail msg = do
  err <- getError
  fPutStr stderr $ msg ++ " failed:" ++ err
  fflush stderr
  System.exit 1

width : Int
width = 400

height : Int
height = 400

pman : Player
pman = Play 10 10

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
        sequence_ (drawBoard board width height renderer)
        drawPlayer pman board width height renderer
        SDL2.renderPresent renderer
        loop renderer
