import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepOnePlusDet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.LastLen

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma herm_splitForm_inv_mulVec_eq_of_mem {k r : ℕ} {g : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hg : g ∈ _root_.BranchingSupport.GG k r) (w : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ w) (g⁻¹ *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w w := by
  have hgH : gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r := hg
  have hdet : IsUnit g.det := _root_.GlobalTheory.TensLen.isUnit_det_of_unitary (_root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq k r) hgH
  have h := _root_.Formalism.FourierDecayAlt.P.SettingConstruction.form_of_unitary (_root_.Formalism.QuantumDeterminants.Hpk k r) hgH (g⁻¹ *ᵥ w) (g⁻¹ *ᵥ w)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  exact h.symm

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma splitForm_mulVec_apply_eq_sgn_mul_sig (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) :
    (_root_.Formalism.QuantumDeterminants.Hpk k r *ᵥ u) i = _root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) := by
  simp only [Matrix.mulVec, dotProduct, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma herm_splitForm_eq_sum_star_mul_sgn_mul_sig (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) u u = ∑ i, star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)) := by
  unfold _root_.Formalism.QuantumDeterminants.herm
  simp only [dotProduct, Pi.star_apply, splitForm_mulVec_apply_eq_sgn_mul_sig]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma herm_splitForm_sub_eq_of_isotropic {k r : ℕ} (z y : Fin (2 * r + k + 1) → ℂ)
    (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hy : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (z - y) (z - y) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) z z := by
  have hz' : ∀ i : Fin (2 * r + k + 1), (i : ℕ) < r ∨ r + k < (i : ℕ) → z i = 0 := hz
  rw [herm_splitForm_eq_sum_star_mul_sgn_mul_sig, herm_splitForm_eq_sum_star_mul_sgn_mul_sig]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  by_cases h1 : (i : ℕ) < r
  · have hσ := _root_.Formalism.QuantumDeterminants.GBasic.sig_lo k r i h1
    rw [hz' i (Or.inl h1), hz' (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) (Or.inr (by omega)),
      hy (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) (by omega)]
    simp
  · by_cases h2 : r + k < (i : ℕ)
    · rw [hz' i (Or.inr h2), hy i (by omega)]
      simp
    · rw [_root_.Formalism.QuantumDeterminants.GBasic.sig_mid k r i (by omega) (by omega), hy i (by omega), sub_zero]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma neg_re_herm_splitForm_le_sum_normSq (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) :
    -(_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) u u).re ≤ ∑ i, Complex.normSq (u i) := by
  have hs : ∀ i, ‖_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i‖ = 1 := by
    intro i
    unfold _root_.Formalism.QuantumDeterminants.GBasic.sgn
    split_ifs <;> simp
  have hperm : ∑ i, Complex.normSq (u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)) = ∑ i, Complex.normSq (u i) :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (_root_.Formalism.QuantumDeterminants.GBasic.sig_sig k r)) (fun i => Complex.normSq (u i))
  rw [herm_splitForm_eq_sum_star_mul_sgn_mul_sig, Complex.re_sum, ← Finset.sum_neg_distrib]
  calc ∑ i, -(star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))).re
      ≤ ∑ i, (Complex.normSq (u i) + Complex.normSq (u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))) / 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := Complex.abs_re_le_norm (star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)))
        rw [norm_mul, norm_mul, norm_star, hs, one_mul] at h1
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        nlinarith [neg_le_abs (star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))).re,
          sq_nonneg (‖u i‖ - ‖u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)‖)]
    _ = ∑ i, Complex.normSq (u i) := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hperm]
        ring

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.LastLen.last_len : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), _root_.Formalism.QuantumDeterminants.inWb k r z → 0 < _root_.Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ _root_.BranchingSupport.GG k r, _root_.Formalism.QuantumDeterminants.Tz k r z ≤ _root_.BranchingSupport.lenA k r z g (Fin.last r) ^ 2 ∧ ∀ a, 0 < _root_.BranchingSupport.lenA k r z g a ∧ _root_.BranchingSupport.lenA k r z g a = _root_.Formalism.MainNotions.S.lA k r z g a := by
  intro k r z hz hT g hg
  have hpos := (_root_.GlobalTheory.TensLen.lengths k r z hz hT g hg).2.2.1
  refine ⟨?_, fun a => ⟨hpos a, _root_.BranchingSupport.TensInh.lenA_eq_lA z g a⟩⟩
  have hbound : √(_root_.Formalism.QuantumDeterminants.Tz k r z) ≤ _root_.BranchingSupport.lenA k r z g (Fin.last r) := by
    rw [_root_.BranchingSupport.TensInh.lenA_eq_lA]
    unfold _root_.Formalism.MainNotions.S.lA _root_.Formalism.MainNotions.S.eucl
    refine le_csInf ⟨_, 0, Submodule.zero_mem _, rfl⟩ ?_
    rintro t ⟨y, hy, rfl⟩
    apply Real.sqrt_le_sqrt
    have hy0 : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0 := by
      intro i hi
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        unfold _root_.Formalism.QuantumDeterminants.bvec _root_.Formalism.QuantumDeterminants.eI
        refine Pi.single_eq_of_ne ?_ _
        intro h
        have h' := congrArg Fin.val h
        have := b.1.isLt
        simp only at h'
        omega
      | zero => rfl
      | add x x' _ _ hx hx' => simp [hx, hx']
      | smul c x _ hx => simp [hx]
    have hf : _root_.Formalism.QuantumDeterminants.fvec k r z (Fin.last r) = z := by
      unfold _root_.Formalism.QuantumDeterminants.fvec
      simp
    rw [hf]
    calc _root_.Formalism.QuantumDeterminants.Tz k r z = -(_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ (z - y)) (g⁻¹ *ᵥ (z - y))).re := by
          rw [herm_splitForm_inv_mulVec_eq_of_mem hg, herm_splitForm_sub_eq_of_isotropic z y hz hy0,
            _root_.Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq]
          simp
      _ ≤ _ := neg_re_herm_splitForm_le_sum_normSq k r _
  calc _root_.Formalism.QuantumDeterminants.Tz k r z = √(_root_.Formalism.QuantumDeterminants.Tz k r z) ^ 2 := (Real.sq_sqrt hT.le).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2

end GlobalTheory.LastLen
