module Tile

  data Direction : Type where
    East  : Direction
    South : Direction
    West  : Direction
    North : Direction

  data Color : Type where
    Red   : Color
    White : Color
    Green : Color

  data Suit : Type where
    Character : Suit
    Bamboo    : Suit
    Wheel     : Suit

  -- Tiles are indexed so that a single tile cannot be reused for scoring,
  -- and to differentiate akadoras in the case of 5s
  data Tile : Type where
    Wind   : Direction -> Fin 4 -> Tile
    Dragon : Color -> Fin 4 -> Tile
    Suited : Suit -> Fin 9 -> Fin 4 -> Tile
