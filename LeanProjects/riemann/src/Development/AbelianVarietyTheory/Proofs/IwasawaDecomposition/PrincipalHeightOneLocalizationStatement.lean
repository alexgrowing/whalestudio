import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalHeightOneLocalization
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_height_one_localization : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : Ideal R) [Q.IsPrime], IsDiscreteValuationRing (Localization.AtPrime Q) → ∀ {W : Type} [CommRing W] [IsDomain W] (ϖ : W), Irreducible ϖ → ∀ g : R →+* W, Function.Injective g → (∀ r, r ∉ Q → IsUnit (g r)) → (∃ π ∈ Q, Associated (g π) ϖ) → ∀ h : R, h ≠ 0 → ∀ n : ℕ, Associated (g h) (ϖ ^ n) → (Ideal.span {h}).map (algebraMap R (Localization.AtPrime Q)) = maximalIdeal (Localization.AtPrime Q) ^ n := by
  first | exact @GlobalTheory.span_map_localization_eq_maximalIdeal_pow | exact GlobalTheory.span_map_localization_eq_maximalIdeal_pow | (intros; apply GlobalTheory.span_map_localization_eq_maximalIdeal_pow <;> assumption)
