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
  -- The Fin 4 keeps track of how many tiles have been drawn from the dead wall
  -- by a Kan. If a 5th Kan is called, the hand ends with no win. Furthermore,
  -- the Fin 4 is used in determinining the number and locations of the dora
  -- indicators.
  data DeadWall : Fin 4 -> Type where
    MkDeadWall : Vect 14 Tile -> (fn : Fin 4) -> DeadWall fn

  -- Pops a tile off the live wall, tile will become the active tile for the
  -- player drawing it.
  draw : { [STATE (Wall (S n))] ==>
           [STATE (Wall n)] } Eff m Tile
  draw = do
    (MkWall (x :: xs)) <- get
    putM (MkWall xs)
    pure x

  -- Pops a tile off the dead wall and adds the /last/ tile in the live wall
  -- to the /end/ of the dead wall. Only happens after a Kan is called. The
  -- resulting tile will become the active tile for the player who called the
  -- Kan.
  deadWallDraw : { ['wall ::: STATE (Wall (S n)),
                 'deadWall ::: STATE (DeadWall (weaken fn))] ==>
                 ['wall ::: STATE (Wall n),
                 'deadWall ::: STATE (DeadWall (fS fn))] } Eff m Tile
  deadWallDraw = do
    (MkWall xs) <- 'wall :- get
    let xs' = init xs
    let x'  = last xs
    (MkDeadWall (y :: ys) (fS n)) <- 'deadWall :- get
    'deadWall :- put (MkDeadWall (ys ++ [x']) (?rhs2))
    'wall :- putM (MkWall xs')
    pure y

  doraIndicators : Bool -> DeadWall fn -> List Tile
