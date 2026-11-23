import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsMultihomogPrimeOfPlace
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multihomog_prime_of_place : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K) (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) → ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧ (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧ ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e → (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre <;> assumption)
