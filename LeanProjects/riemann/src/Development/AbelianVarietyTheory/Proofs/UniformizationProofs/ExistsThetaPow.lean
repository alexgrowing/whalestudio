import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPow

theorem prod_fam_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.famφ D F 0 i) ^ DegPre.famε k i = h (DegPre.prB D F).left ^ k := by
  have hmul : ∀ {T : Over (Spec (CommRingCat.of R))} (a b : T ⟶ D.P.A), padd D.P.A a b = a * b := by
    intro T a b
    unfold padd
    rfl
  have hc0 : D.c 0 = 1 := by
    have h2 := D.c_add 0 0
    rw [add_zero, hmul] at h2
    exact mul_eq_left.mp h2.symm
  have h1 : toUnit (DegPre.BF D F) ≫ D.c 0 = toUnit (DegPre.BF D F) ≫ η[D.P.A] := by
    rw [hc0]
    rfl
  have h3 : padd D.P.A (DegPre.prB D F) (toUnit (DegPre.BF D F) ≫ η[D.P.A]) = DegPre.prB D F := by
    rw [hmul]
    exact mul_one _
  have hφ : DegPre.famφ D F 0 = ![(DegPre.prB D F).left, (DegPre.prB D F).left,
      (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left, (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left] := by
    unfold DegPre.famφ
    rw [h1, h3]
  have hε : DegPre.famε k = ![(k : ℤ) - 1, 1, -1, 1] := rfl
  rw [Fin.prod_univ_four, hφ, hε]
  show h (DegPre.prB D F).left ^ ((k : ℤ) - 1) * h (DegPre.prB D F).left ^ (1 : ℤ) *
      h (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left ^ (-1 : ℤ) * h (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left ^ (1 : ℤ) =
      h (DegPre.prB D F).left ^ k
  simp only [zpow_neg, zpow_one]
  rw [_root_.inv_mul_cancel_right, ← zpow_add_one, sub_add_cancel, zpow_natCast]

theorem exists_theta_pow : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∃ (θ : LB.Sec (D.P.L.pull (DegPre.prB D F).left)) (σ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε n))), (∃ j, θ.f j ≠ 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval σ r z J = sval (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left) (ε := fun _ => 1) θ r z J ^ n := by
  intro hT R _ _ D F _ _ n _
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.FamFree.exists_sec_ne_zero (D := D) (F := F) hT (k := 1) le_rfl 0
  have hF₁ : FormEq (DegPre.famφ D F 0) (DegPre.famε 1)
      (fun _ : PUnit => (DegPre.prB D F).left) (fun _ => (1 : ℤ)) := by
    intro U _ h
    rw [prod_fam_zero D F 1 h]
    simp
  obtain ⟨θ, hθ⟩ := exists_sec D.P.isLB hF₁ s₀
  have hθne : ∃ j, θ.f j ≠ 0 := by
    by_contra hc
    push Not at hc
    have g0 : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), gs f y U 0 = 0 := by
      intro Y X f y U
      unfold gs
      split <;> simp
    apply hs₀
    intro j
    refine (sec_ext_val D.P.isLB (s' := H1.SectionArithmetic.secZero _) (fun y J hJ => ?_) j).trans rfl
    rw [← hθ _ (𝟙 _) y J hJ]
    exact ((congrArg (gs _ y _) (hc _)).trans (g0 _ _ _)).trans (g0 _ _ _).symm
  let P := H1.SectionArithmetic.powSec (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left)
    (ε := fun _ => (1 : ℤ)) (fun _ : Fin n => θ)
  have hFn : FormEq (fun p : Fin n × PUnit => (DegPre.prB D F).left) (fun _ => (1 : ℤ))
      (DegPre.famφ D F 0) (DegPre.famε n) := by
    intro U _ h
    rw [prod_fam_zero D F n h]
    simp
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hFn P
  refine ⟨θ, σ, hθne, fun Z r z J hJ => ?_⟩
  rw [hσ Z r z J hJ, H1.SectionArithmetic.sval_powSec _ r z hJ]
  simp

end GlobalTheory.ThetaPow
