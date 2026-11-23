import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineDegreeInvariantFiniteExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
open NumberField IsDedekindDomain Module GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLine_degree_invariant_finite_extension : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k'] (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ), (∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓) → ∀ (r : (k →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 k) → ℝ), (Function.support fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)).Finite → (Function.support ρ).Finite ∧ lineDeg r ρ = lineDeg (fun s : k' →+* ℂ => r (s.comp (algebraMap k k'))) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) := by
  first | exact @GlobalTheory.FlatLine.lineDeg_descent | exact GlobalTheory.FlatLine.lineDeg_descent | (intros; apply GlobalTheory.FlatLine.lineDeg_descent <;> assumption)
