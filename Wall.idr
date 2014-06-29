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
  lteUnsuccL : LTE (S a) b -> LTE a b
  lteUnsuccL (lteSucc x) = lteSuccR x
  -- actually this makes sense when you replace lteSuccR with its value:
  -- lteUnsuccL : LTE (S a) b -> LTE a b
  -- lteUnsuccL (lteSucc lteZero) = lteZero -- (a < b because a is zero)
  -- lteUnsuccL (lteSucc x) = lteSucc (lteUnsuccL x)

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
    'deadWall :- putM (MkDeadWall (ys ++ [x']) zs (?length14,lteUnsuccL lt4))
    'wall :- putM (MkWall xs')
    pure z

  odds : Vect n a -> (m ** (Vect m a, Either (m = divNat n 2) (m = divNat n 2 + 1)))
  odds []         = Ex_intro _ ([], Left refl)
  odds (x::[])    = Ex_intro _ ([x], Right refl)
  odds (x::y::xs) = case odds xs of
                         (_ ** (ys,Left l)) => Ex_intro _ (x::ys,?lprf)
                         (_ ** (ys,Right r)) => Ex_intro _ (x::ys,?rprf)

  natToFinSafe : (n : Nat) -> (m : Nat) -> LTE n (S m) -> Fin (S m)
  natToFinSafe Z Z lteZero = fZ
  natToFinSafe Z (S k) lteZero = fZ
  natToFinSafe (S k) Z (lteSucc x) = fZ
  natToFinSafe (S k) (S j) (lteSucc x) = fS $ natToFinSafe k j x

  inv_natToFinSafe_finToNat : {m : Nat} -> {n : Nat} ->
                              (prf : LTE n (S m)) -> (fn : Fin (S m)) -> (n = finToNat fn) ->
                              (natToFinSafe n m prf = fn)
  inv_natToFinSafe_finToNat prf1 fn prf2 = ?rhs

  fromJust : {a : Type} -> {y : a} -> (x : Maybe a) -> (x = Just y) -> a
  fromJust (Just y) refl = y
  fromJust x prf = ?fromJust_rhs

  -- the number of dora indicators is one plus the number of kans called; the
  -- number of kans called is the number of tiles drawn from the dead wall; the
  -- dead wall starts out with 4 drawable tiles. Thus the number of dora
  -- indicators is 1 + 4 - n = 5 - n, where n represents the number of drawable
  -- tiles left in the deadwall
  doraIndicators : DeadWall n -> (m ** (Vect m Tile, m = 5 - n))
  doraIndicators (MkDeadWall xs _ _) {n=n} = let (m ** (ys,_)) = odds xs in
                                             let minus5nFin = natToFinSafe (5 - n) m ?ltm in
                                             (_ ** (take minus5nFin ys, ?minus5n))

---------- Proofs ----------

Wall.length14 = proof
  intros
  compute -- plus (n + 1) a = 14  ==> plus (plus n 1) a = 14
  rewrite plusCommutative 1 n1 -- ==> plus (S n) a = 14
  compute                      -- ==> S (plus n a) = 14
  rewrite sym (plusSuccRightSucc n1 a) -- ==> plus n (S a) 14
  refine len14
