import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.SupG

theorem norm_cls_sq_eq {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {K : Mat n → V}
    (h : MemLp (fun y : G n => K y.val) 2 μ) :
    ‖cls μ K‖ ^ 2 = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := integral_nonneg fun y => by positivity
  have hc : cls μ K = h.toLp _ := dif_pos h
  rw [hc, Lp.norm_toLp, h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

theorem exists_unit {n : ℕ} {x : Mat n} (hx : x ∈ GLs n) : ∃ g : G n, g.val = x :=
  ⟨((Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)).unit, rfl⟩

theorem sup_sq_bound : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure], ∃ (S : Finset (List (Bool × Fin n × Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (h : Mat n → V), ContDiffOn ℝ ∞ h (GLs n) → (∀ w, MemLp (fun y : G n => Rw w h y.val) 2 μ) → ∀ x ∈ GLs n, ‖h x‖ ^ 2 ≤ C * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 := by
  intro hS n _ _ μ _
  obtain ⟨S, r, C, hC⟩ := hS n μ
  refine ⟨S, max C 0, le_max_right _ _, fun V _ _ _ h hsm hL x hx => ?_⟩
  obtain ⟨g, rfl⟩ := exists_unit hx
  have h0 := hC V h hsm g.val hx
  have hw : ∀ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ ≤
      ‖cls μ (Rw w h)‖ ^ 2 := by
    intro w _
    set K := Rw w h with hK
    have hm : MemLp (fun y : G n => K y.val) 2 μ := hL w
    have hφ : Integrable (fun y : G n => ‖K y.val‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hm.1).1 hm
    have hψ : Integrable (fun y : G n => ‖K (g.val * y.val)‖ ^ 2) μ := by
      simpa only [Units.val_mul] using hφ.comp_mul_left g
    have e1 : ∫ y : G n, ‖K (g.val * y.val)‖ ^ 2 ∂μ = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
      simpa only [Units.val_mul] using
        integral_mul_left_eq_self (μ := μ) (fun y : G n => ‖K y.val‖ ^ 2) g
    rw [norm_cls_sq_eq hm, ← e1]
    exact setIntegral_le_integral hψ (Filter.Eventually.of_forall fun y => by positivity)
  have hI : 0 ≤ ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
    Finset.sum_nonneg fun w _ => integral_nonneg fun y => by positivity
  calc ‖h g.val‖ ^ 2
      ≤ C * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ := h0
    _ ≤ max C 0 * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hI
    _ ≤ max C 0 * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (le_max_right _ _)

end GlobalTheory.CompanionTheory.PresSobA.SupG
