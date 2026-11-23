import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceMultiplicationDerivativeWordIteratedFDeriv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_multiplicationDerivativeWord_iteratedFDeriv : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (u : κ → mixedEmbedding.mixedSpace F) (i : ℕ) (vs : List (κ → mixedEmbedding.mixedSpace F))
        (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
            vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x := by
  first | exact @GlobalTheory.WeilL2Words.slice_word_mul_fderivs | exact GlobalTheory.WeilL2Words.slice_word_mul_fderivs | (intros; apply GlobalTheory.WeilL2Words.slice_word_mul_fderivs <;> assumption)
