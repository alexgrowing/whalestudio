import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem tst_conj_Kinf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) {β : Lie E a → ℂ} (hβ : ConjInv β) (k : Kinf E a) (y : GA E a) :
    tst U β ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k))) = tst U β y := by
  have e : ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k)))⁻¹ =
      (infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k) := by group
  have hf : GeneralLinearGroup.map (pFin E) ((infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k)) =
      GeneralLinearGroup.map (pFin E) y⁻¹ := by
    simp only [map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]
  have hi : GeneralLinearGroup.map (pInf E) ((infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k)) =
      (Unitary.toUnits k)⁻¹ * GeneralLinearGroup.map (pInf E) y⁻¹ * Unitary.toUnits k := by
    rw [map_mul, map_mul, map_inv, pInf_infGL]
  have hc := hβ k⁻¹ (toL (GeneralLinearGroup.map (pInf E) y⁻¹).val)
  have hv : toL ((k⁻¹ : Kinf E a).1 * Matrix.of (toL (GeneralLinearGroup.map (pInf E) y⁻¹).val) * star (k⁻¹ : Kinf E a).1) =
      toL ((Unitary.toUnits k)⁻¹ * GeneralLinearGroup.map (pInf E) y⁻¹ * Unitary.toUnits k).val := by
    have h1 : ((Unitary.toUnits k)⁻¹ : GL (Fin a) (Cinf E)).val = (k⁻¹ : Kinf E a).1 := by
      rw [← map_inv]; rfl
    have h2 : star (k⁻¹ : Kinf E a).1 = k.1 := by
      change star (star k.1) = k.1
      exact star_star _
    rw [h2, Units.val_mul, Units.val_mul, h1]
    rfl
  unfold tst ker
  rw [e, hf, hi, ← hv, hc]

theorem convR_tst_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ), ConjInv β → ∀ (F : L2 (latticeGL E a) μ) (k : Kinf E a) (x : GA E a), convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)) x = convR μ (tst U β) (lift (latticeGL E a) F) (x * infGL E a (Unitary.toUnits k)) := by
  intro E _ _ _ a μ _ _ U β hβ F k x
  have h1 : ∀ᵐ y ∂μ, lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F) (x * y) =
      lift (latticeGL E a) F (x * y * infGL E a (Unitary.toUnits k)) :=
    (measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (lift_R (infGL E a (Unitary.toUnits k)) F)
  simp only [AutomorphicL2Unitary.convR]
  rw [← integral_mul_left_eq_self
      (fun y => tst U β y * lift (latticeGL E a) F (x * infGL E a (Unitary.toUnits k) * y)) (infGL E a (Unitary.toUnits k))⁻¹,
    ← integral_mul_right_eq_self
      (fun y => tst U β ((infGL E a (Unitary.toUnits k))⁻¹ * y) *
        lift (latticeGL E a) F (x * infGL E a (Unitary.toUnits k) * ((infGL E a (Unitary.toUnits k))⁻¹ * y)))
      (infGL E a (Unitary.toUnits k))]
  refine integral_congr_ae (h1.mono fun y hy => ?_)
  have e : x * infGL E a (Unitary.toUnits k) * ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k))) =
      x * y * infGL E a (Unitary.toUnits k) := by group
  simp only [tst_conj_Kinf U hβ k y, e, hy]

end GlobalTheory.CompanionTheory.SmoothRep
