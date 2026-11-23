import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealSupportFinite
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logIdeal_support_finite : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero <;> assumption)
