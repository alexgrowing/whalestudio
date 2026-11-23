import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperatorRationalPoint_laws : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB (heisS a b φ) ∧ (∀ τ ∈ Siegel ι, ∀ ζ, thS (heisS a b φ) τ ζ = cexp (π * I * ∑ k, (qv (b k) ⬝ᵥ τ *ᵥ qv (b k) + 2 * (qv (b k) ⬝ᵥ ζ k) + qv (a k) ⬝ᵥ qv (b k))) * thS φ τ (fun k => ζ k + qv (a k) + τ *ᵥ qv (b k))) ∧ (∀ a' b', heisS a b (heisS a' b' φ) = cexp (π * I * ((∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k) : ℚ) : ℂ)) • heisS (a + a') (b + b') φ) ∧ heisS 0 0 φ = φ ∧ ∀ ψ, IsSB ψ → ip (heisS a b φ) (heisS a b ψ) = ip φ ψ := by
  first | exact @GlobalTheory.SW.heisS_laws | exact GlobalTheory.SW.heisS_laws | (intros; apply GlobalTheory.SW.heisS_laws <;> assumption)
