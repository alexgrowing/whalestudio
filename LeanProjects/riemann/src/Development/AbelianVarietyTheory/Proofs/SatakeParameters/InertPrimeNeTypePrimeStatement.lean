import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNeTypePrime
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_prime_ne_typePrime : ∀ (D : D7) (l : ℕ) (k : Fin 2), TwistedPlaces.InertK D l → l ≠ D.host.g k := by
  first | exact @GlobalTheory.InertNotType.main | exact GlobalTheory.InertNotType.main | (intros; apply GlobalTheory.InertNotType.main <;> assumption)
