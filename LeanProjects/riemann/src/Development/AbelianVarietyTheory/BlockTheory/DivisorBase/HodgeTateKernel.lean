import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.EigenSplit GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

section AtPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {Λ : Type} [CommRing Λ] [StarRing Λ]

def IsOpenFiniteFlatSubgroup (G : Over (Sp O)) [GrpObj G] (N : ℕ) {H : Over (Sp O)}
    (j : H ⟶ torsion G N) : Prop :=
  IsOpenImmersion j.left ∧ IsFinite H.hom ∧ Flat H.hom ∧
    (∀ S : Over (Sp O), ∃ z : S ⟶ H, z ≫ j ≫ torsion.ι G N = 1) ∧
    (∀ (S : Over (Sp O)) (x y : S ⟶ H), ∃ z : S ⟶ H,
      z ≫ j ≫ torsion.ι G N = (x ≫ j ≫ torsion.ι G N) * (y ≫ j ≫ torsion.ι G N)) ∧
    (∀ (S : Over (Sp O)) (x : S ⟶ H), ∃ z : S ⟶ H,
      z ≫ j ≫ torsion.ι G N = (x ≫ j ≫ torsion.ι G N)⁻¹)

def IsCharacter (G : Over (Sp O)) [GrpObj G] (N : ℕ) {H : Over (Sp O)} (j : H ⟶ torsion G N)
    (χ : H ⟶ Gm (Sp O)) : Prop :=
  ∀ (S : Over (Sp O)) (x y z : S ⟶ H),
    z ≫ j ≫ torsion.ι G N = (x ≫ j ≫ torsion.ι G N) * (y ≫ j ≫ torsion.ι G N) →
      z ≫ χ = (x ≫ χ) * (y ≫ χ)

omit [Fact p.Prime] in
theorem isNilpotent_dual {R : Type} [CommRing R] {n : ℕ} (h : (p : R) ^ n = 0) :
    IsNilpotent (p : DualNumber R) :=
  ⟨n, by rw [← map_natCast (algebraMap R (DualNumber R)), ← map_pow, h, map_zero]⟩

variable [Algebra ℤ_[p] O] (P : Point p v O Λ)

def alLeft : P.T →ₗ[ℤ_[p]] omega P.Gt := -P.al₀

def LevelReduction : Prop :=
  ∀ (n : ℕ) (H : Over (Sp O)) (j : H ⟶ torsion P.G (p ^ n)),
    IsOpenFiniteFlatSubgroup P.G (p ^ n) j →
    ∀ (t : P.T) (χ : H ⟶ Gm (Sp O)), IsCharacter P.G (p ^ n) j χ →
      (∀ (w : specO O O ⟶ H) (z : Pts P.A.A),
        z.left ≫ P.gen = spMap (algebraMap O C) ≫ (w ≫ j ≫ torsion.ι P.G (p ^ n)).left →
          algebraMap O C (unitOf (w ≫ χ) : O) = (weil P.A (p ^ n) (t.lev n) z : C)) →
      ∀ (R : Type) [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0) (x : LieG P.Gt)
        (w : specO O (DualNumber R) ⟶ H),
        w ≫ j ≫ torsion.ι P.G (p ^ n) =
          P.cmp (DualNumber R) (isNilpotent_dual hR) (ptMap (dualBC (Algebra.ofId O R)) ≫ x.1) →
        (unitOf (w ≫ χ) : DualNumber R) =
          TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (algebraMap O R ((alLeft P t).1 x))

omit [Algebra ℤ_[p] O] in

def RestrictionOnto : Prop := Function.Surjective P.weilChar

def CokernelBound : Prop := ∀ f : omega P.Gt, (p : O) ^ 2 • f ∈ LinearMap.range P.al

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

def KernelShape : Prop :=
  Module.finrank C P.W = P.A.g ∧
    (∀ (a : Λ), ∀ x ∈ P.W, P.actV a x ∈ P.W) ∧
    P.tateTorus.baseChange C ≤ P.W ∧
    P.W ≤ P.tateGt.baseChange C ∧
    (∀ x : P.V, x ∈ P.W ↔ ∀ y ∈ P.W, P.pairV x y = 0) ∧
    (∀ τ : Λ →+* O, Module.finrank C (P.eigW τ) = AvDefs.rTau P.Gt P.oGt τ) ∧
    P.W = Submodule.span C (Set.range P.bLie)

example (a : Λ) (x : P.V) (hx : x ∈ P.W) : P.actV a x ∈ P.W := by
  change P.alC _ = 0
  rw [P.isEquivariant_alC a x, show P.alC x = 0 from hx, map_zero]

example (t : P.T) : alLeft P t = 0 ↔ P.al₀ t = 0 := by
  simp [alLeft]

end AtPoint

def HodgeTateKernelAtPoint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0)
    (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C]
    [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ),
    LevelReduction P ∧ RestrictionOnto P ∧ CokernelBound P ∧ KernelShape P

end GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel
