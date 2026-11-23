import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.NonVan
open GlobalTheory.UT.CoefBasic

theorem val_powFrame {S : Scheme.{0}} {A : Over S} (L : LB A.left) {T : Over S} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (powFrame A L x τ k) r z J = val τ r z J ^ k :=
  map_zpow _ _ _

theorem exists_sec_ne_zero : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 4 ≤ k → ∀ (x : TFK (R := R) F ⟶ A.A) (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))), e.IsGen → ∃ (t : SecA A F k) (c : F), c ≠ 0 ∧ (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val) := by
  intro hL R _ _ A F _ _ k hk x e he
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' A.isLB (Z := (TFK (R := R) F).left) z
  obtain ⟨t, ht⟩ := GlobalTheory.TwistUnit.unitAt_pow hL.1.ample A k hk (snd (TFK (R := R) F) A.A).left
    ((ptSecT A.A x).left z)
  have hu := GlobalTheory.TwistUnit.isUnit_sval_of A.isLB t (ptSecT A.A x).left z ht J' hJ'
  obtain ⟨c, hc⟩ := cstH_surj z (hu.unit * (val e (𝟙 _) z J' ^ (k : ℤ))⁻¹).val
  refine ⟨t, c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := pt_eq (R := R) z z'
    have a₁ := sval_tr t (ptSecT A.A x).left hJ hJ'
    have a₂ := val_tr he (𝟙 _) hJ hJ'
    have hx : (ptSecT A.A x).left ≫ (snd (TFK (R := R) F) A.A).left = x.left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    rw [Fin.prod_univ_one, hx, ← hu.unit_spec] at a₁
    rw [Fin.prod_univ_one, Category.id_comp, zpow_one] at a₂
    have a₃ : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) =
        (hu.unit * (val e (𝟙 _) z J' ^ (k : ℤ))⁻¹).val := (cst_eq z c).trans hc
    refine a₁.trans ?_
    rw [a₃, val_powFrame, a₂, ← Units.val_mul, ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module

end GlobalTheory.UT.NonVan
end
