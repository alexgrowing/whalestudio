import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentity
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_alternating_series_identity : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E) (n : ℕ) (L : Lat O K r), 1 ≤ n → ∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2)) • heckeElem k (heckeAll (n - k) φ) L = 0 := by
  first | exact @GlobalTheory.HeckeSeries.heckeSeries_identity | exact GlobalTheory.HeckeSeries.heckeSeries_identity | (intros; apply GlobalTheory.HeckeSeries.heckeSeries_identity <;> assumption)
