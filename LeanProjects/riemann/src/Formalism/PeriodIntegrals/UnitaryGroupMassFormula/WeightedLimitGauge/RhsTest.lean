import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

theorem wI_injective : Function.Injective (wI k r) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [PI.RhsWLim.wI] at h'
  exact Fin.ext (by omega)

theorem sum_wb (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by
  have h1 : ∑ j : Fin (k + 1), f (PI.RhsWLim.wI k r j) = ∑ i ∈ Finset.univ.image (PI.RhsWLim.wI k r), f i :=
    (Finset.sum_image (fun a _ b _ h => wI_injective h)).symm
  rw [h1]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro i _ hi
  apply hf
  by_contra hc
  apply hi
  rw [Finset.mem_image]
  exact ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [PI.RhsWLim.wI]; omega)⟩

theorem tau_wI (j : Fin (k + 1)) : HU.tau k r (wI k r j) = wI k r j := by
  have hj := j.isLt
  apply Fin.ext
  show (if r + j.val < r ∨ r + k < r + j.val then 2 * r + k - (r + j.val) else r + j.val) = r + j.val
  rw [if_neg (by omega)]

theorem hpk_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = HU.sgn k r i * v (HU.tau k r i) := by
  simp [Matrix.mulVec, dotProduct, PI.RhsWLim.W.HU.hpk_row, ite_mul]

theorem sgn_wI (j : Fin (k + 1)) : HU.sgn k r (wI k r j) = if j = Fin.last k then -1 else 1 := by
  by_cases h : j = Fin.last k
  · subst h
    simp [PI.RhsWLim.W.HU.sgn, PI.RhsWLim.wI]
  · have hne : j.val ≠ k := fun e => h (Fin.ext (by rw [Fin.val_last]; exact e))
    simp [PI.RhsWLim.W.HU.sgn, PI.RhsWLim.wI, h, hne]

theorem herm_wb (v z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) v z = herm (Hb k) (wbPart k r v) (wbPart k r z) := by
  simp only [PI.RhsWLim.herm, dotProduct]
  rw [sum_wb (k := k) (r := r)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.star_apply, hpk_mulVec_apply, PI.RhsWLim.Hb, Matrix.mulVec_diagonal, PI.RhsWLim.wbPart,
      sgn_wI, tau_wI]
  · intro i hi
    simp [hz i hi]

theorem embWb_wI (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (j m : Fin (k + 1)) :
    embWb k r μ (wI k r j) (wI k r m) = μ j m := by
  have hj := j.isLt
  have hm := m.isLt
  have hc : (r ≤ (PI.RhsWLim.wI k r j).val ∧ (PI.RhsWLim.wI k r j).val ≤ r + k) ∧
      (r ≤ (PI.RhsWLim.wI k r m).val ∧ (PI.RhsWLim.wI k r m).val ≤ r + k) := by
    simp only [PI.RhsWLim.wI]
    omega
  unfold PI.RhsWLim.embWb
  rw [dif_pos hc]
  exact congrArg₂ μ (Fin.ext (by simp [PI.RhsWLim.wI])) (Fin.ext (by simp [PI.RhsWLim.wI]))

theorem wbPart_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') :
    wbPart k r (embWb k r μ *ᵥ z') = μ *ᵥ wbPart k r z' := by
  funext j
  simp only [PI.RhsWLim.wbPart, Matrix.mulVec, dotProduct]
  rw [sum_wb (k := k) (r := r)]
  · simp only [embWb_wI]
  · intro i hi
    simp [hz' i hi]

theorem herm_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (embWb k r μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  rw [herm_wb _ _ hz, wbPart_emb μ z' hz']

theorem herm_fix {h : Mat k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ u) z = herm (Hpk k r) u z := by
  obtain ⟨hU, -, hfix⟩ := hh
  have hU' : hᴴ * PI.RhsWLim.Hpk k r * h = PI.RhsWLim.Hpk k r := hU
  unfold PI.RhsWLim.herm
  calc star z ⬝ᵥ (PI.RhsWLim.Hpk k r *ᵥ (h *ᵥ u))
      = star (h *ᵥ z) ⬝ᵥ (PI.RhsWLim.Hpk k r *ᵥ (h *ᵥ u)) := by rw [hfix]
    _ = star z ⬝ᵥ ((hᴴ * PI.RhsWLim.Hpk k r * h) *ᵥ u) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = star z ⬝ᵥ (PI.RhsWLim.Hpk k r *ᵥ u) := by rw [hU']

theorem inv_fix {h : Mat k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) : h⁻¹ *ᵥ z = z := by
  obtain ⟨hU, -, hfix⟩ := hh
  have hdet := PI.RhsWLim.W.HU.isUnit_of_uh hU
  calc h⁻¹ *ᵥ z = h⁻¹ *ᵥ (h *ᵥ z) := by rw [hfix]
    _ = z := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul h hdet, Matrix.one_mulVec]

theorem circle_null (c : ℝ) : (volume : Measure ℂ) {ζ | Complex.normSq ζ = c} = 0 := by
  have hsub : {ζ : ℂ | Complex.normSq ζ = c} ⊆ Metric.sphere (0 : ℂ) (Real.sqrt c) := by
    intro ζ hζ
    have hζ' : Complex.normSq ζ = c := hζ
    rw [mem_sphere_zero_iff_norm, ← hζ', Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg ζ)]
  exact measure_mono_null hsub (Measure.addHaar_sphere volume 0 _)

private theorem pairF_mul_embWb_mul_inv {z z' : Fin (2 * r + k + 1) → ℂ} (hz : PI.RhsWLim.inWb k r z) (hz' : PI.RhsWLim.inWb k r z')
    {p q : PI.RhsWLim.Mat k r} (hp : p ∈ PI.RhsWLim.UWset k r z) (hq : q ∈ PI.RhsWLim.UWset k r z')
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    pairF k r z z' (fun i j => (p * PI.RhsWLim.embWb k r μ * q⁻¹) i j) =
      PI.RhsWLim.herm (PI.RhsWLim.Hb k) (μ *ᵥ PI.RhsWLim.wbPart k r z') (PI.RhsWLim.wbPart k r z) := by
  show PI.RhsWLim.herm (PI.RhsWLim.Hpk k r) ((p * PI.RhsWLim.embWb k r μ * q⁻¹) *ᵥ z') z = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, herm_fix hp,
    inv_fix hq, herm_emb μ z z' hz hz']

theorem rhsTest : RhsTest := by
  intro k r z z' μW μW' a a' μsec hD g hg
  simp only [PI.RhsWLim.rhsW]
  obtain ⟨-, -, hnW, -⟩ := hD.haarW
  obtain ⟨-, -, hnW', -⟩ := hD.haarW'
  obtain ⟨-, hS⟩ := hD.sec
  have hW : ∀ᵐ x ∂μW, Matrix.of x ∈ PI.RhsWLim.UWset k r z := ae_iff.mpr hnW
  have hW' : ∀ᵐ x ∂μW', Matrix.of x ∈ PI.RhsWLim.UWset k r z' := ae_iff.mpr hnW'
  have hae : ∀ᵐ ζ : ℂ, Complex.normSq ζ ≠ PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z' := by
    rw [ae_iff]
    simpa using circle_null (PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z')
  rw [← lintegral_const_mul' (ENNReal.ofReal (a * a')) _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hae] with ζ hζ
  try dsimp only
  by_cases hreg : PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z' < Complex.normSq ζ
  · have hsec := (hS ζ hreg).2
    rw [lintegral_congr_ae (μ := μW) (g := fun _ => g ζ * ENNReal.ofReal a') ?_]
    · rw [lintegral_const, hD.massW, ENNReal.ofReal_mul hD.a_pos.le]
      ring
    · filter_upwards [hW] with h hh
      try dsimp only
      rw [lintegral_congr_ae (μ := μW') (g := fun _ => g ζ) ?_]
      · rw [lintegral_const, hD.massW']
      · filter_upwards [hW'] with h' hh'
        exact (congrArg g (pairF_mul_embWb_mul_inv hD.z_mem hD.z'_mem hh hh' (μsec ζ))).trans (congrArg g hsec)
  · have hle : ¬ (PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z' ≤ Complex.normSq ζ) :=
      fun hle => hreg (lt_of_le_of_ne hle (Ne.symm hζ))
    have h0 : PI.RhsWLim.zWeight k (PI.RhsWLim.Tz k r z) (PI.RhsWLim.Tz k r z') ζ = 0 := by
      unfold PI.RhsWLim.zWeight
      exact if_neg hle
    simp [h0]

end PI.RhsWLim.W
