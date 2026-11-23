import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

namespace ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory

def LB.genPull {X Y : Scheme.{u}} (M : LB X) (c : LB.Gen M) (f : Y ⟶ X) : LB.Gen (M.pull f) where
  s := fun j => res (LB.wchart_le M (K := PUnit) (fun _ => f) j PUnit.unit) (pullU f _ (c.s (j PUnit.unit)))

section Biext

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def law1φ {T : Over S} (x x' y : T ⟶ G) : ULift.{u} (Fin 3) → (T.left ⟶ (G2 G).left) :=
  fun k => (![lift (padd G x x') y, lift x y, lift x' y] k.down).left

def law2φ {T : Over S} (x y y' : T ⟶ G) : ULift.{u} (Fin 3) → (T.left ⟶ (G2 G).left) :=
  fun k => (![lift x (padd G y y'), lift x y, lift x y'] k.down).left

def lawε : ULift.{u} (Fin 3) → ℤ := fun k => ![1, -1, -1] k.down

structure IsBiext (P : LB (G2 G).left) where

  isLB : P.IsLB
  law1 : LB.Gen (LB.LinComb P (law1φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε)
  law2 : LB.Gen (LB.LinComb P (law2φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε)
  isGen1 : law1.IsGen
  isGen2 : law2.IsGen

  assoc1 : LB.Gen.Corr P _ _ _ _
    (LB.mulGen P _ _ _ _
      (LB.pullGen P _ _ law1 (lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3))).left)
      (LB.pullGen P _ _ law1 (lift (x4 G 0) (lift (x4 G 1) (x4 G 3))).left))
    (LB.mulGen P _ _ _ _
      (LB.pullGen P _ _ law1 (lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3))).left)
      (LB.pullGen P _ _ law1 (lift (x4 G 1) (lift (x4 G 2) (x4 G 3))).left))

  comm1 : LB.Gen.Corr P _ _ _ _ law1
    (LB.pullGen P _ _ law1 (lift (x3 G 1) (lift (x3 G 0) (x3 G 2))).left)

  assoc2 : LB.Gen.Corr P _ _ _ _
    (LB.mulGen P _ _ _ _
      (LB.pullGen P _ _ law2 (lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3))).left)
      (LB.pullGen P _ _ law2 (lift (x4 G 0) (lift (x4 G 1) (x4 G 2))).left))
    (LB.mulGen P _ _ _ _
      (LB.pullGen P _ _ law2 (lift (x4 G 0) (lift (x4 G 1) (padd G (x4 G 2) (x4 G 3)))).left)
      (LB.pullGen P _ _ law2 (lift (x4 G 0) (lift (x4 G 2) (x4 G 3))).left))

  comm2 : LB.Gen.Corr P _ _ _ _ law2
    (LB.pullGen P _ _ law2 (lift (x3 G 0) (lift (x3 G 2) (x3 G 1))).left)

  compat : LB.Gen.Corr P _ _ _ _
    (LB.mulGen P _ _ _ _
      (LB.mulGen P _ _ _ _
        (LB.pullGen P _ _ law1 (lift (x4 G 0) (lift (x4 G 1) (padd G (x4 G 2) (x4 G 3)))).left)
        (LB.pullGen P _ _ law2 (lift (x4 G 0) (lift (x4 G 2) (x4 G 3))).left))
      (LB.pullGen P _ _ law2 (lift (x4 G 1) (lift (x4 G 2) (x4 G 3))).left))
    (LB.mulGen P _ _ _ _
      (LB.mulGen P _ _ _ _
        (LB.pullGen P _ _ law2 (lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3))).left)
        (LB.pullGen P _ _ law1 (lift (x4 G 0) (lift (x4 G 1) (x4 G 2))).left))
      (LB.pullGen P _ _ law1 (lift (x4 G 0) (lift (x4 G 1) (x4 G 3))).left))

end Biext

section DVR

variable (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]

abbrev etaK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of V) :=
  Spec.map (CommRingCat.ofHom (algebraMap V K))

variable (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
  [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]

abbrev genA : Scheme.{u} := pullback G.hom (etaK V K)
abbrev jA : genA V K G ⟶ G.left := pullback.fst G.hom (etaK V K)

def eK : Spec (CommRingCat.of K) ⟶ G.left := etaK V K ≫ eSec G

abbrev genericFiberCubeInclusion : pullback (G3 G).hom (etaK V K) ⟶ (G3 G).left := pullback.fst (G3 G).hom (etaK V K)

end DVR

end

end ReciprocityTheory.ChartRestriction.G.Semi
