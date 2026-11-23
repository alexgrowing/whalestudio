import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricNumberZeroFinrank
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_number_zero_finrank : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 → ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ (b : Fin 0 → B → ℤ) [IsLocalRing (locRing (mCoordIdeal w) W)] [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], geoNum 0 W b = (Module.finrank (ZMod p) (ResidueField (locRing (mCoordIdeal w) W)) : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank <;> assumption)
