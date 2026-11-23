import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFiniteIdeleFactorization
import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_finite_idele_factorization : ∀ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∃ (r : ℚˣ) (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
    (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧ ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧
    t = Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom r * u := by
  first | exact @GlobalTheory.RatIdele.exists_rat_mul_intUnit | exact GlobalTheory.RatIdele.exists_rat_mul_intUnit | (intros; apply GlobalTheory.RatIdele.exists_rat_mul_intUnit <;> assumption)
