import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeEqSpanOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' : ∀ (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R), GeneralizingMap q → ∀ x : X, Order.coheight x ≤ 1 → (q x).asIdeal ≠ ⊥ → ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  first | exact @GlobalTheory.exists_prime_eq_span_of_coheight_le_one | exact GlobalTheory.exists_prime_eq_span_of_coheight_le_one | (intros; apply GlobalTheory.exists_prime_eq_span_of_coheight_le_one <;> assumption)
