import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLocalEpsilonFactorMulTameChar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateLocalEpsilonFactor_mul_tameChar : ∀ (E : Type) [Field E] [NumberField E] (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) (s : ℂ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → (q : 𝓞 E) ∉ w.asIdeal ^ 2 → ExpAt χ w 2 → ξ.TameAt w → ExpAt (χ * ξ) w 2 ∧ ∃ y : Eˣ, locEps (χ * ξ) w 2 s = ((ξ.locK w y : ℂˣ) : ℂ) * locEps χ w 2 s := by
  first | exact @GlobalTheory.TameTwist.locEps_mul_tame | exact GlobalTheory.TameTwist.locEps_mul_tame | (intros; apply GlobalTheory.TameTwist.locEps_mul_tame <;> assumption)
