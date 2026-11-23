import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeightOneValuationsControlSubgroup
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heightOne_valuations_control_subgroup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (J : Type) [Finite J] (g : J → (FractionRing R)ˣ), ∃ (s : ℕ) (v : Fin s → ((FractionRing R)ˣ →* Multiplicative ℤ)), (∀ i (x : (FractionRing R)ˣ) (r : R), (x : FractionRing R) = algebraMap R _ r → 0 ≤ Multiplicative.toAdd (v i x)) ∧ (∀ x ∈ Subgroup.closure (Set.range g), (∀ i, 0 ≤ Multiplicative.toAdd (v i x)) → ∃ r : R, (x : FractionRing R) = algebraMap R _ r) := by
  first | exact @GlobalTheory.HtVal.exists_vals | exact GlobalTheory.HtVal.exists_vals | (intros; apply GlobalTheory.HtVal.exists_vals <;> assumption)
