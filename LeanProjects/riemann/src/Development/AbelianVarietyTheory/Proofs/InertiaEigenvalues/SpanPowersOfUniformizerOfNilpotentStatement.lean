import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPowersOfUniformizerOfNilpotent
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_mul_pow_of_residue_surjective_of_nilpotent : ∀ (C B : Type) [CommRing C] [CommRing B] (φ : C →+* B) (π : B) (L : C) (e m : ℕ), (∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π}) → π ^ e ∈ Ideal.span {φ L} → φ L ^ m = 0 → ∀ x : B, ∃ c : Fin e → C, x = ∑ j, φ (c j) * π ^ (j : ℕ) := by
  first | exact @GlobalTheory.span_powers_of_uniformizer_of_nilpotent | exact GlobalTheory.span_powers_of_uniformizer_of_nilpotent | (intros; apply GlobalTheory.span_powers_of_uniformizer_of_nilpotent <;> assumption)
