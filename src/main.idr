module Main
import Board
import Graphics.SDL2 as SDL2
import System as System
import Data.Vect as Vect
import Data.Matrix as Matrix
import Data.Matrix.Numeric
import Data.Fin
import Debug.Trace

drawCircle : (x : Nat) -> (y : Nat) -> (r : Nat) -> Int -> Int -> Int -> Renderer -> IO ()
drawCircle x y rad r g b ren = SDL2.filledEllipse ren (cast x) (cast y) (cast rad) (cast rad) r g b 255

drawRect : (x : Int) -> (y : Int) -> (w : Int) -> (h : Int) -> Int -> Int -> Int -> Renderer -> IO ()
drawRect x y w h r g b ren = SDL2.filledRect ren y x w h r g b 255

drawSquare : (m : Nat) -> (n : Nat) -> (bw : Nat) -> (bh : Nat) -> (ren : Renderer) -> (Nat, Nat, Int) -> IO ()
drawSquare m n bw bh ren (x,y,isWall) = let
  blockX : Nat = x * bw
  blockY : Nat = y * bh
in do
  drawRect (cast blockX) (cast blockY) (cast bw) (cast bh) (255*isWall) 0 0 ren


drawBoard : SphereMat n m Int -> (w : Nat) -> (h : Nat) -> Renderer -> List (IO ())
drawBoard m0 w h {n} {m} = \ren => let
  widthPerBlock : Nat = w `div` m
  heightPerBlock : Nat = h `div` n
in
  map (drawSquare m n widthPerBlock heightPerBlock ren) (matToList m0)

data Direction = Up | Down | Left | Right
%name Direction dir,dir0

{- Player x y-}
data Player = Play Nat Nat
%name Player p,p'

{- State player score -}
data GameState = State Player Nat
%name GameState s,s'

execMovePlayer : (w : Nat) -> (h : Nat) -> Direction -> Player -> Player
execMovePlayer w h Up (Play x Z) = Play x h
execMovePlayer w h Up (Play x (S k)) = Play x k
execMovePlayer w h Down (Play x y) = Play x (S y)
execMovePlayer w h Left (Play Z y) = Play w y
execMovePlayer w h Left (Play (S k) y) = Play k y
execMovePlayer w h Right (Play x y) = Play (S x) y

movePlayer : SphereMat w h Int -> Direction -> Player -> Player
movePlayer m0 Up p@(Play x Z) {w = w} {h = h} = if isTraversable m0 x h
                                                   then Play x h
                                                   else p
movePlayer m0 Up p@(Play x (S k)) {w = w} {h = h} = if isTraversable m0 x k
                                                     then Play x k
                                                     else p
movePlayer m0 Down p@(Play x y) {w = w} {h = h} = if isTraversable m0 x (S y)
                                                   then Play x (S y)
                                                   else p
movePlayer m0 Left p@(Play Z y) {w = w} {h = h} = if isTraversable m0 w y
                                                   then Play w y
                                                   else p
movePlayer m0 Left p@(Play (S k) y) {w = w} {h = h} = if isTraversable m0 k y
                                                       then Play k y
                                                       else p
movePlayer m0 Right p@(Play x y) {w = w} {h = h} = if isTraversable m0 (S x) y
                                                      then Play (S x) y
                                                      else p

{-drawCircle : (x : Int) -> (y : Int) -> (r : Int) -> Int -> Int -> Int -> Renderer -> IO ()-}

drawPlayer : Player -> SphereMat n m Int -> (w : Nat) -> (h : Nat) -> Renderer -> IO ()
drawPlayer (Play x y) m0 w h ren {n = n} {m = m} = let
                                                        bw : Nat = w `div` m
                                                        bh : Nat = h `div` n
                                                        cx : Nat = (x `mod` m)*bw + (bw `div` 2)
                                                        cy : Nat = (y `mod` n)*bh + (bh `div` 2)
                                                        r : Nat = (min bw bh) `div` 2
                                                        in
                                                        drawCircle cx cy r 0 255 0 ren


fail : (msg: String) -> IO ()
fail msg = do
  err <- getError
  fPutStr stderr $ msg ++ " failed:" ++ err
  fflush stderr
  System.exit 1

width : Nat
width = 400

height : Nat
height = 400

pman : Player
pman = Play 1 1

beginState : GameState
beginState = State pman 0

updateGhosts : GameState -> GameState
updateGhosts s = s

mapPlayer : (Player -> Player) -> GameState -> GameState
mapPlayer f (State p x) = (State (f p) x)

main : IO ()
main = (do
  renderer <- SDL2.init (cast width) (cast height)
  loop beginState renderer
  SDL2.destroyRenderer renderer
  quit)
    where
      loop : GameState -> Renderer -> IO ()
      loop s@(State player score) renderer = do
        {- Drawing -}
        False <- SDL2.pollEventsForQuit | pure ()
        True <- SDL2.setRendererDrawColor renderer 0 0 111 255
          | fail "setRendererDrawColor"
        SDL2.renderClear renderer
        sequence_ (drawBoard board width height renderer)
        drawPlayer player board width height renderer
        SDL2.renderPresent renderer

        {- NOTE FOR COLLISION DETECTION: don't check object positions. Check them modulo the board size. -}

        {- Event handling and game logic-}
        let mp = movePlayer board
        event <- SDL2.pollEvent
        case event of
             Just (SDL2.KeyDown SDL2.KeyUpArrow) => do
               loop (mapPlayer (mp Up) s) renderer

             Just (SDL2.KeyDown SDL2.KeyDownArrow) => do
               loop (mapPlayer (mp Down) s) renderer

             Just (SDL2.KeyDown SDL2.KeyRightArrow) => do
               loop (mapPlayer (mp Right) s) renderer

             Just (SDL2.KeyDown SDL2.KeyLeftArrow) => do
               loop (mapPlayer (mp Left) s) renderer
             _ => do loop s renderer
