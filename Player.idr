module Player

  import Effect.State
  import Tile

  -- A hand consists of 13 tiles, including open tiles.
  --
  -- A just-drawn tile is not included until kept in the hand after discard,
  -- and the 4th tile in a declared Kan is not included.
  --
  -- This enables us to guarantee that players will never have the wrong number
  -- of tiles at the end of their turn, while simultaneously giving us the
  -- information to determine whether a player is in tenpai (one tile from
  -- winning).
  data Hand : Type where
    MkHand : Vect 13 Tile -> Hand

  -- The Discard Pile increases by 1 for each discard which is not called
  data DiscardPile : Nat -> Type where
    MkDiscard : Vect n Tile -> DiscardPile n

  -- Pushes a tile onto the discard pile, should only occur /after/ tile has
  -- been submitted for calling by other players
  discard : Tile -> { [STATE (DiscardPile n)] ==>
            [STATE (DiscardPile (S n))] } Eff m ()
  discard x = do
    (MkDiscard xs) <- get
    putM (MkDiscard (x :: xs))

