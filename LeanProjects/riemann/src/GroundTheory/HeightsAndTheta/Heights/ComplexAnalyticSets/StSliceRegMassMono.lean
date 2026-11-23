import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem SliceCut.monotone {n : ℕ} (h : HermNorm n) (x : Fin n → ℂ) : Monotone fun k => sliceCut h k x := by
  intro k m hkm
  simp only [sliceCut]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkm 1
  rcases le_or_gt 0 (Real.log (h.dualNorm x)) with hL | hL
  · apply Real.smoothTransition.monotone
    have := div_le_div_of_nonneg_left hL hk hkm'
    linarith
  · have h1 : ∀ j : ℕ, Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((j : ℝ) + 1)) = 1 := fun j =>
      Real.smoothTransition.one_of_one_le (by
        have : Real.log (h.dualNorm x) / ((j : ℝ) + 1) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hL.le (by positivity)
        linarith)
    rw [h1 k, h1 m]

def SliceRegMassMono.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (ε : ℝ)
    (a b : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → 0 < ε →
    Measurable a → Measurable b → (∀ x, 0 ≤ a x) → (∀ x, a x ≤ b x) → (∀ x, b x ≤ 1) →
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a (fun _ x => Real.log (h.dualNorm x)) ≤
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b (fun _ x => Real.log (h.dualNorm x))

end

end GroundTheory.Heights₂.Heights
