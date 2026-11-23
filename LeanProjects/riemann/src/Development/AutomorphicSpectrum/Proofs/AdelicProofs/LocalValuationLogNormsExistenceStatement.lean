import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocalValuationLogNormsExistence
import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_valuation_log_norms_existence : ∀ (K : Type) [Field K] [NumberField K] (r : (K →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ), (∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]), ∃ (la : HeightOneSpectrum (𝓞 K)) (π : K), (∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) ∧ la.valuation K π = WithZero.exp (-1 : ℤ)) ∧ (∃ N : LogNorms K, (∀ σ, N.inf σ = Real.log (r σ)) ∧ ∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 K)) (π : K), (∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation K π = WithZero.exp (-1 : ℤ) → N.fin p κ = ρ la * Real.log ‖κ π‖) ∧ ∀ N : LogNorms K, (∀ σ, N.inf σ = Real.log (r σ)) → (∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 K)) (π : K), (∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation K π = WithZero.exp (-1 : ℤ) → N.fin p κ = ρ la * Real.log ‖κ π‖) → (N.IsAdelic ↔ (Function.support ρ).Finite) ∧ (N.IsAdelic → N.deg = GlobalTheory.FlatLine.lineDeg r ρ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.Dd.deg_dict | exact GlobalTheory.CompanionTheory.Ar.Br.Dd.deg_dict | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.Dd.deg_dict <;> assumption)
