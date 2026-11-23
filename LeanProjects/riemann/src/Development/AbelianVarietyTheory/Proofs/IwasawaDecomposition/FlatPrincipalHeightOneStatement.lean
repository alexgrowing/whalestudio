import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatPrincipalHeightOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemAssociatedOfMapEq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_principal_height_one : ∀ {A R : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (φ : A →+* R), φ.Flat → IsLocalHom φ → ∀ h : R, h ≠ 0 → (∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap φ = ⊥ → h ∉ Q) → (∀ q : Ideal A, q ≠ ⊥ → ∃ n : ℕ, ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap φ = q → (Ideal.span {h}).map (algebraMap R (Localization.AtPrime Q)) = (q ^ n).map ((algebraMap R (Localization.AtPrime Q)).comp φ)) → ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → ∃ a : A, h ∣ φ a ∧ ∃ s ∉ Q, φ a ∣ s * h := by
  first | exact @GlobalTheory.PrincipalDescent.exists_dvd_dvd_of_height_eq_one | exact GlobalTheory.PrincipalDescent.exists_dvd_dvd_of_height_eq_one | (intros; apply GlobalTheory.PrincipalDescent.exists_dvd_dvd_of_height_eq_one <;> assumption)
