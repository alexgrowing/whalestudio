import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.IteratedFDerivIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace

noncomputable section

open scoped ContDiff
open MeasureTheory Set Filter Topology

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {κ' κ'' : Type} [Fintype κ'] [Fintype κ'']

def sc (s : ℝ) : κ' ⊕ κ'' → ℝ := Sum.elim (fun _ => 1) (fun _ => s)

def Ain (s : ℝ) : (κ' ⊕ κ'' → W) →L[ℝ] (κ' ⊕ κ'' → W) :=
  ContinuousLinearMap.pi fun j => sc s j • ContinuousLinearMap.proj j

theorem Ain_apply (s : ℝ) (x : κ' ⊕ κ'' → W) (j : κ' ⊕ κ'') : Ain s x j = sc s j • x j := rfl

theorem norm_Ain_apply_le {s : ℝ} (hs : |s| ≤ 1) (x : κ' ⊕ κ'' → W) : ‖Ain s x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => ?_
  rw [Ain_apply, norm_smul]
  have h1 : ‖sc s j‖ ≤ 1 := by
    cases j with
    | inl _ => simp [sc]
    | inr _ => simpa [sc, Real.norm_eq_abs] using hs
  calc ‖sc s j‖ * ‖x j‖ ≤ 1 * ‖x j‖ := by gcongr
    _ = ‖x j‖ := one_mul _
    _ ≤ ‖x‖ := norm_le_pi_norm x j

theorem norm_Ain_le {s : ℝ} (hs : |s| ≤ 1) : ‖(Ain s : (κ' ⊕ κ'' → W) →L[ℝ] (κ' ⊕ κ'' → W))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  exact (norm_Ain_apply_le hs x).trans (one_mul _).ge

theorem norm_le_max_Ain (s : ℝ) (x : κ' ⊕ κ'' → W) : ‖x‖ ≤ max ‖Ain s x‖ ‖x ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun j => ?_
  cases j with
  | inl i =>
    have h : Ain s x (Sum.inl i) = x (Sum.inl i) := by
      rw [Ain_apply]
      simp [sc]
    rw [← h]
    exact (norm_le_pi_norm (Ain s x) _).trans (le_max_left _ _)
  | inr i =>
    exact (norm_le_pi_norm (x ∘ Sum.inr) i).trans (le_max_right _ _)

theorem contDiff_Ain : ContDiff ℝ ∞ fun p : (κ' ⊕ κ'' → W) × ℝ => Ain p.2 p.1 := by
  refine contDiff_pi.2 fun j => ?_
  simp only [Ain_apply]
  rcases j with j | j
  · simp only [sc, Sum.elim_inl, one_smul]
    exact (contDiff_apply ℝ W (Sum.inl j)).comp contDiff_fst
  · simp only [sc, Sum.elim_inr]
    exact contDiff_snd.smul ((contDiff_apply ℝ W (Sum.inr j)).comp contDiff_fst)

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
