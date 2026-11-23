import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumLogEmbeddingsEqNorm
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.RatProductFormulaStatement
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem product_formula_embeddings (k : Type) [Field k] [NumberField k] (x : k) (hx : x ≠ 0) :
    {p | (LogNorms.ofElt x).finSum p ≠ 0}.Finite ∧
      (∑ s : k →+* ℂ, Real.log ‖s x‖) + ∑ᶠ p, (LogNorms.ofElt x).finSum p = 0 := by
  have hN : Algebra.norm ℚ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have hfin : ∀ p : Nat.Primes, (LogNorms.ofElt x).finSum p =
      Real.log ‖((Algebra.norm ℚ x : ℚ) : ℂ_[p])‖ := fun p =>
    sum_log_norm_embeddings_eq_log_norm k ℂ_[p] x hx
  have hinf := sum_log_norm_embeddings_eq_log_norm k ℂ x hx
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rat_product_formula (Algebra.norm ℚ x) hN
  simp only [hfin]
  exact ⟨h1, by rw [hinf]; exact h2⟩

end GlobalTheory.CompanionTheory.Ar.Fl
