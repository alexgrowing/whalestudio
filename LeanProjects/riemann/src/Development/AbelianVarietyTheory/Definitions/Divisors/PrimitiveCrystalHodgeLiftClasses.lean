import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

variable {R : Type} [CommRing R] {I : Ideal R}

def primitiveCrystalHodgeLiftClasses (κ : DividedPowers I) {S : Scheme.{0}} {t : S ⟶ Sp R} (A₀ : Over S) [GrpObj A₀] (X : Over (Sp R))
    (i : A₀.left ⟶ X.left) (w : i ≫ X.hom = A₀.hom ≫ t) : Submodule R (prim κ t A₀) :=
  ((F1 (X.hom ≫ 𝟙 _)).map (IsMor.of_dividedPowersZeroIdeal (s := X.hom ≫ 𝟙 _) κ (s' := A₀.hom ≫ t) (σ := RingHom.id R) (φ := i)
    (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, w])).pull1).comap (prim κ t A₀).subtype

def schemeFil (κ : DividedPowers I) {S : Scheme.{0}} {t : S ⟶ Sp R} (A₀ : Over S) [GrpObj A₀] (X : Over (Sp R))
    (i : A₀.left ⟶ X.left) (w : i ≫ X.hom = A₀.hom ≫ t) : Submodule R (Crys κ t A₀) :=
  (primitiveCrystalHodgeLiftClasses κ A₀ X i w).dualAnnihilator

theorem schemeFil_eq_liftFil (κ : DividedPowers I) {S : Scheme.{0}} {t : S ⟶ Sp R} {A₀ : Over S} [GrpObj A₀]
    {A : Over (Sp R)} [GrpObj A] {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A t i) (hp : AllPrim (dp0 R) (𝟙 _) A) :
    schemeFil κ A₀ A i h.1.w = liftFil κ h := by
  ext d
  change d ∈ (primitiveCrystalHodgeLiftClasses κ A₀ A i h.1.w).dualAnnihilator ↔ crysToDR κ h d ∈ (PrimitiveSubmodule A).dualAnnihilator
  rw [Submodule.mem_dualAnnihilator, Submodule.mem_dualAnnihilator]
  constructor
  · intro hd x hx
    rw [crysToDR_apply]
    apply hd
    show (((liftMor κ h).pull x : prim κ t A₀) : Cris.H1 κ (A₀.hom ≫ t)) ∈
      (F1 (A.hom ≫ 𝟙 _)).map (IsMor.of_dividedPowersZeroIdeal (s := A.hom ≫ 𝟙 _) κ (s' := A₀.hom ≫ t) (σ := RingHom.id R)
        (φ := i) (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, h.1.w])).pull1
    rw [GrpMor.coe_pull]
    exact Submodule.mem_map_of_mem hx
  · intro hd y hy
    have hy' : (y : Cris.H1 κ (A₀.hom ≫ t)) ∈
        (F1 (A.hom ≫ 𝟙 _)).map (IsMor.of_dividedPowersZeroIdeal (s := A.hom ≫ 𝟙 _) κ (s' := A₀.hom ≫ t)
          (σ := RingHom.id R) (φ := i)
          (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, h.1.w])).pull1 := hy
    obtain ⟨c, hc, hcy⟩ := Submodule.mem_map.mp hy'
    have hcp : c ∈ primDR A := by
      rw [show primDR A = ⊤ from hp]
      exact Submodule.mem_top
    have key := hd ⟨c, hcp⟩ hc
    rw [crysToDR_apply] at key
    have hpy : (liftMor κ h).pull ⟨c, hcp⟩ = y := by
      apply Subtype.ext
      rw [GrpMor.coe_pull]
      exact hcy
    rw [hpy] at key
    exact key

def NilExp (κ : DividedPowers I) (N : ℕ) : Prop :=
  ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) → N ≤ (l.map Prod.fst).sum → (l.map fun p ↦ κ.dpow p.1 p.2).prod = 0

theorem isPDNilpotent_iff (κ : DividedPowers I) : IsNilDP κ ↔ ∃ N, NilExp κ N := Iff.rfl

structure IsStep {R₁ R₀ : Type} [CommRing R₁] [CommRing R₀] (κ : DividedPowers I) (π : R →+* R₀) {J : Ideal R}
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) {I₁ : Ideal R₁} (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀) : Prop where
  nil : IsNilDP κ
  nil₁ : IsNilDP κ₁
  surj : Function.Surjective ρ
  surj₁ : Function.Surjective π₁
  comp : π₁.comp ρ = π
  ker : RingHom.ker π = I
  kerJ : RingHom.ker ρ = J
  ker₁ : RingHom.ker π₁ = I₁
  dp : IsDPMorphism κ κ₁ ρ
  dpJ : IsDPMorphism (divided₂ hJ) κ (RingHom.id R)

def SqLifting : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
      GlobalTheory.Published.GrothendieckMessing.LiftObj (divided₂ h) π ∧ GlobalTheory.Published.GrothendieckMessing.LiftHom (divided₂ h) π

end GlobalTheory.SqLift
