import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
import Formalism.FormalDegreeBessel.FinalG

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem regular_pos_compl : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Gf k r z z' γ ≠ 0 → 0 < Gf k r z z' γ ∧ Dmin k r z z' γ (Fin.last (r + 1)) ≠ 0 ∧ IsUnit (gramM k r z z' γ).det ∧ ∀ y : Fin (2 * r + k + 1) → ℂ, y ≠ 0 → (∀ i, herm (Hpk k r) y (gramVec k r z z' γ i) = 0) → 0 < (herm (Hpk k r) y y).re := by
  intro k r z z' γ hz hz' hT hT' hγ hG

  have hGpos : 0 < Gf k r z z' γ :=
    lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg k r z z' hz hz' hT hT' γ hγ) (Ne.symm hG)

  have hdet : (gramM k r z z' γ).det ≠ 0 := by
    intro h0
    apply hG
    have hg := Formalism.QuantumDeterminants.gGram k r z z' hz hz' γ hγ
    rw [h0, mul_zero] at hg
    exact_mod_cast hg

  have hk : 1 ≤ k := by
    by_contra hk0
    have hk' : k = 0 := by omega
    subst hk'
    apply hdet
    have hunit : ¬ IsUnit (gramM 0 r z z' γ) := by
      intro hu
      have h1 := Matrix.rank_of_isUnit _ hu
      rw [Formalism.QuantumDeterminants.gn_gramM_eq] at h1
      have h2 := Matrix.rank_mul_le_right
        ((Formalism.QuantumDeterminants.gnB 0 r z z' γ)ᴴ * Hpk 0 r) (Formalism.QuantumDeterminants.gnB 0 r z z' γ)
      have h3 := Matrix.rank_le_card_height (Formalism.QuantumDeterminants.gnB 0 r z z' γ)
      simp only [Fintype.card_sum, Fintype.card_fin] at h1 h3
      omega
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hunit
    exact hunit
  refine ⟨hGpos, ?_, isUnit_iff_ne_zero.mpr hdet, ?_⟩
  ·
    intro h0
    have hG' := hGpos
    unfold Gf at hG'
    rw [h0, map_zero] at hG'
    have hTT := mul_pos hT hT'
    have hn := Complex.normSq_nonneg (Dmin k r z z' γ ⟨r, by omega⟩)
    nlinarith
  ·
    intro y hy horth
    have hmem : y ∈ Formalism.FourierDecayAlt.C2.Uperp k r z z' γ := by
      rw [Formalism.FourierDecayAlt.C2.Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
      funext i
      rw [Pi.zero_apply, ← horth i]
      simp [herm, Matrix.mulVec, dotProduct]
    exact (Formalism.FourierDecayAlt.P.gram_independent_signature' k r z z' γ ⟨hk, ⟨hz, hT⟩, ⟨hz', hT'⟩⟩ ⟨hγ, hGpos⟩).2.2.1 y hmem hy

end GlobalTheory.SgInf
