import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

abbrev kb (p : ℕ) [Fact p.Prime] : Type := IsLocalRing.ResidueField (OO p)

abbrev rPt (p : ℕ) [Fact p.Prime] : Sp (kb p) ⟶ Sp (OO p) := spMap (IsLocalRing.residue (OO p))

def Ser {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (N : ℕ) {J : Type} (cls : J → X) {C : Type} [NormedField C]
    (w : J → C) (ν : X →+ ℝ) : Prop :=
  ∃ (t : X → J → C) (κ : ℝ), 0 < κ ∧ (∀ i, HasSum (fun α => t α i) (w i)) ∧
    (∀ α i, t α i ≠ 0 → ∃ m, α = cls i + N • m) ∧
    ∀ α, (∀ i, ‖t α i‖ ≤ κ * Real.exp (-((q α - q (cls i)) / N + ν α))) ∧
      ∃ i, ‖t α i‖ = κ * Real.exp (-((q α - q (cls i)) / N + ν α))
attribute [local instance] SplitExt.free SplitExt.finite

structure Mod (p : ℕ) [Fact p.Prime] {V : Type} [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G]
    (g N : ℕ) {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) {J : Type} [Fintype J]
    (σ : J → H.Sec) (cls : J → X) where
  isLB : H.IsLB
  smooth : SmoothOfRelativeDimension g G.hom
  Φ : FibPre (kb p)
  r : Φ.G.left ⟶ G.left
  cart : IsGrpPullback Φ.G G (rPt p ≫ spMap j) r
  xe : Φ.E.X ≃+ X
  F : J → (Φ.H 1).Sec
  good : Φ.Good N (q.comp xe.toIntLinearEquiv.toLinearMap) (fun i => xe.symm (cls i)) F
  pol : Φ.Pol N
  dim : pol.PB.g + Module.finrank ℤ Φ.E.X = g
  red : ∀ (x : Φ.Pt) (v : J → kb p), Crd (Φ.H 1) F x.left v → Crd H σ (x.left ≫ r) v
  ser : ∀ a : Sp (PadicAlgCl p) ⟶ G.left, a ≫ G.hom = gPt p ≫ spMap j → ∀ w, Crd H σ a w →
    ∃ ν : X →+ ℝ, Ser q N cls w ν ∧ ((∃ m, ∀ α, ν α = QuadraticMap.polar q m α) →
      ∃ c : Sp (OO p) ⟶ G.left, c ≫ G.hom = spMap j ∧ gPt p ≫ c = a)
end GlobalTheory.ZH
end
