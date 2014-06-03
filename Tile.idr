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

  data Tile : Type where
    Wind   : Direction -> Tile
    Dragon : Color -> Tile
    Suited : Suit -> Fin 9 -> Tile
