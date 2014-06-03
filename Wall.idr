module Wall
  -- This module contains the types and operations on the live wall & dead wall.

  import Effect.State
  import Tile

  -- The wall's size starts at 70 and decreases by 1 for each draw or Kan
  data Wall : Nat -> Type where
    MkWall : Vect n Tile -> Wall n

  -- The dead wall's size is fixed, but tiles can be swapped out in the case
  -- of a Kan, where one tile is added from the end of the live wall to the end
  -- of the dead wall, and one tile is taken from the front of the live wall to
  -- become the active tile for the player who called the Kan.
  --
  -- The first/last 4 tiles in the deadwall at the beginning of the game are
  -- special in that they can be drawn from in the event of a Kan, so we
  -- maintain that as a separate vector with the invariant that the two vectors
  -- have a combined length of 14
  data DeadWall : Nat -> Type where
    MkDeadWall : Vect n Tile -> Vect m Tile -> (n + m = the Nat 14, LTE m 4) -> DeadWall m

  -- Pops a tile off the live wall, tile will become the active tile for the
  -- player drawing it.
  draw : { [STATE (Wall (S n))] ==>
           [STATE (Wall n)] } Eff m Tile
  draw = do
    (MkWall (x :: xs)) <- get
    putM (MkWall xs)
    pure x

  -- shamelessly copied from the idris2048 implementation
  -- https://github.com/KesterTong/idris2048
  total
  lteSuccR : LTE a b -> LTE a (S b)
  lteSuccR lteZero = lteZero
  lteSuccR (lteSucc x) = lteSucc (lteSuccR x)

  -- This is used below to prove that the length of the deadwall draw tiles
  -- stays below 4 when it decreases from a value already below 4.
  --
  -- not exactly sure how idris was able to reduce LTE (S a) b -> LTE a b
  -- to LTE a (S b), but that made things easy since I already know how
  -- lteSuccR is defined from idris2048. Neat!
  total
  lteSuccL : LTE (S a) b -> LTE a b
  lteSuccL (lteSucc x) = lteSuccR x

  -- Pops a tile off the dead wall and adds the /last/ tile in the live wall
  -- to the /end/ of the dead wall. Only happens after a Kan is called. The
  -- resulting tile will become the active tile for the player who called the
  -- Kan.
  deadWallDraw : { ['wall ::: STATE (Wall (S n)),
                 'deadWall ::: STATE (DeadWall (S a))] ==>
                 ['wall ::: STATE (Wall n),
                 'deadWall ::: STATE (DeadWall a)] } Eff m Tile
  deadWallDraw = do
    (MkWall xs) <- 'wall :- get
    let xs' = init xs
    let x'  = last xs
    (MkDeadWall ys (z :: zs) (len14,lt4)) <- 'deadWall :- get
    'deadWall :- putM (MkDeadWall (ys ++ [x']) zs (?length14,lteSuccL lt4))
    'wall :- putM (MkWall xs')
    pure z

  doraIndicators : Bool -> DeadWall n -> List Tile
