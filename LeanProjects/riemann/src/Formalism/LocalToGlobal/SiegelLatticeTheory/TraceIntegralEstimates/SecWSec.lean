import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ}
  {w w' : Fin k → Fin n → ℂ} {sc T T' : ℝ}

def Mv (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (w w' : Fin k → Fin n → ℂ)
    (sc T T' : ℝ) (i0 : Fin k) (c : Fin (r + 1) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fr2M ε e f z' w' (e2 sc c f) (p2 sc c e) (z2 T T' c z w i0) (w2 T T' c z w i0) T'

theorem famSc_castSucc (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (b : Fin r) :
    famSc sc e z (Fin.castSucc b) = sfv sc b • e b := by
  simp only [famSc, fam, Fin.snoc_castSucc, Fin.coe_castSucc, sfv]

theorem famSc_last (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc sc e z (Fin.last r) = z := by
  simp only [famSc, fam, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]

theorem zhat_Mv (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hsc : 0 < sc) {c : Fin (r + 1) → ℂ} (i0 : Fin k) :
    Zhat ε (famSc sc e z) (famSc sc e z') (Mv ε e f z z' w w' sc T T' i0 c) = Matrix.diagonal c := by
  have hMe : ∀ b, Mv ε e f z z' w w' sc T T' i0 c *ᵥ e b = e2 sc c f b := fun b => frameChangeMatrix_isotropic F1 b
  have hMz : Mv ε e f z z' w w' sc T T' i0 c *ᵥ z' = z2 T T' c z w i0 := fr2M_mulVec_z F1
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 F0.T_ne
  have hfe : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0 := F0.ep
  ext a b
  simp only [Zhat]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last =>
      rw [famSc_last, famSc_last, hMz]
      simp only [z2, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.zz, F0.zw, mul_zero, add_zero, diagonal_apply_eq,
        alv]
      field_simp
    | cast b =>
      rw [famSc_last, famSc_castSucc, mulVec_smul, hMe]
      simp only [e2, UnitaryIsometries.hJ_smul_right, hJ_swap0 (F0.pz b), mul_zero]
      rw [diagonal_apply_ne]
      exact fun h => (Fin.castSucc_lt_last b).ne h.symm
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [famSc_castSucc, famSc_last, hMz]
      simp only [z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.ez, F0.ew, mul_zero,
        add_zero]
      rw [diagonal_apply_ne]
      exact (Fin.castSucc_lt_last a).ne
    | cast b =>
      rw [famSc_castSucc, famSc_castSucc, mulVec_smul, hMe]
      simp only [e2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hfe, conj_sfv]
      by_cases h : a = b
      · subst h
        rw [diagonal_apply_eq, if_pos rfl, lamv]
        have hs : sfv sc a ≠ 0 := sfv_ne hsc a
        field_simp
      · rw [if_neg h, diagonal_apply_ne _ (fun h' => h (Fin.castSucc_injective _ h'))]
        ring

theorem measurable_Mv (i0 : Fin k) :
    Measurable (fun c : Fin (r + 1) → ℂ => Mv ε e f z z' w w' sc T T' i0 c) := by
  have hlam : ∀ a, Measurable (fun c : Fin (r + 1) → ℂ => lamv sc c a) := fun a =>
    (measurable_pi_apply _).div_const _
  have hinv : ∀ a, Measurable (fun c : Fin (r + 1) → ℂ => (conj (lamv sc c a))⁻¹) := fun a =>
    (Complex.continuous_conj.measurable.comp (hlam a)).inv
  have hal : Measurable (fun c : Fin (r + 1) → ℂ => alv T c) := (measurable_pi_apply _).neg.div_const _
  have hbe : Measurable (fun c : Fin (r + 1) → ℂ => bev T T' c) := by
    unfold bev
    exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      ((((measurable_pi_apply _).norm.pow_const 2).div_const _).sub_const _))
  have hcal : Measurable (fun c : Fin (r + 1) → ℂ => conj (alv T c)) := Complex.continuous_conj.measurable.comp hal
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Mv, frameChangeMatrix_entry, syn, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ((Finset.measurable_sum _ fun a _ => ?_).add (Finset.measurable_sum _ fun a _ => ?_)).add ?_ |>.add
    (Finset.measurable_sum _ fun l _ => ?_)
  · simp only [e2, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hlam a).mul measurable_const)
  · simp only [p2, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hinv a).mul measurable_const)
  · simp only [z2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hal.mul measurable_const).add (hbe.mul measurable_const))
  · simp only [w2]
    by_cases hl : l = i0
    · simp only [if_pos hl, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      exact measurable_const.mul (measurable_const.mul ((hbe.mul measurable_const).add
        ((hcal.mul measurable_const).mul measurable_const)))
    · simp only [if_neg hl]
      exact measurable_const

instance matrix_borel (m : ℕ) : BorelSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin m → ℂ))

theorem measurableEmbedding_uMat (ε : Fin n → Bool) :
    MeasurableEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.measurableEmbedding

def secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T) (hT' : 0 < T')
    (hsc : 0 < sc) (i0 : Fin k) (c : Fin (r + 1) → ℂ) : Formalism.REAL.UJ ε :=
  if h : (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then
    UnitaryIsometries.toUJ ε (frameChangeMatrix_isometry F1 (frm2 (sc := sc) F0 hT hT' hsc h.1 h.2 i0) hdim)
  else 1

theorem uMat_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T)
    (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) (c : Fin (r + 1) → ℂ) :
    Formalism.MainNotions.S.uMat (secV F0 F1 hdim hT hT' hsc i0 c) =
      if (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then Mv ε e f z z' w w' sc T T' i0 c else 1 := by
  unfold secV
  split_ifs with h
  · rfl
  · simp [Formalism.MainNotions.S.uMat]

theorem measurable_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k)
    (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) :
    Measurable (secV F0 F1 hdim hT hT' hsc i0) := by
  rw [← (measurableEmbedding_uMat ε).measurable_comp_iff]
  have he : (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) ∘ secV F0 F1 hdim hT hT' hsc i0 =
      fun c => if (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then Mv ε e f z z' w w' sc T T' i0 c
        else 1 := by
    funext c
    exact uMat_secV F0 F1 hdim hT hT' hsc i0 c
  rw [he]
  have hm1 : MeasurableSet {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun l => (measurableSet_singleton 0).compl.preimage (measurable_pi_apply l)
  have hm2 : MeasurableSet {c : Fin (r + 1) → ℂ | 0 < ‖c (Fin.last r)‖ ^ 2 - T * T'} :=
    measurableSet_lt measurable_const ((((measurable_pi_apply _).norm.pow_const 2)).sub_const _)
  have hm : MeasurableSet {c : Fin (r + 1) → ℂ | (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T'} :=
    hm1.inter hm2
  exact Measurable.ite hm (measurable_Mv i0) measurable_const

theorem zhat_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T)
    (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) {c : Fin (r + 1) → ℂ} (hc : ∀ l, c l ≠ 0)
    (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') :
    Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat (secV F0 F1 hdim hT hT' hsc i0 c)) =
      Matrix.diagonal c := by
  rw [uMat_secV, if_pos ⟨hc, hg⟩]
  exact zhat_Mv F0 F1 hsc i0

end Formalism.L2.S.Pv.SecW
