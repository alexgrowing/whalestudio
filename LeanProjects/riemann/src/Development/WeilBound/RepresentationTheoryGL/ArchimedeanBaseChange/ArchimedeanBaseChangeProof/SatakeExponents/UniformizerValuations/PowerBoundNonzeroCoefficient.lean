import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds

noncomputable section

open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def PowerBoundNonzeroCoefficient : Prop := ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
  (ι : Type) [Fintype ι] [Nonempty ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (R : ∀ s, B →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (J : Type) [Fintype J] (c : J → ℂ) (q : J → (B →ₐ[ℂ] ℂ)),
  (∀ b, ∃ (C : ℝ) (N : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖∑ j, c j * q j b ^ k‖ ≤ C * (1 + k) ^ N * (Finset.univ.sup' Finset.univ_nonempty fun s => ‖R s b‖) ^ k) →
  ∀ p : B →⋆ₐ[ℂ] ℂ, ∑ j with q j = (p : B →ₐ[ℂ] ℂ), c j ≠ 0 → ∃ s, ∀ b, ‖p b‖ ≤ ‖R s b‖

end PositivityTheory.Rg.BcB.F

end
