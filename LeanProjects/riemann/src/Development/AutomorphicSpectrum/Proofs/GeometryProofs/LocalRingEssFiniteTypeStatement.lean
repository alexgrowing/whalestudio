import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingEssFiniteType
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_ring_ess_finite_type : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (c : ∀ k, J k), (mCoordIdeal w).IsPrime → W.IsPrime → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing <;> assumption)
