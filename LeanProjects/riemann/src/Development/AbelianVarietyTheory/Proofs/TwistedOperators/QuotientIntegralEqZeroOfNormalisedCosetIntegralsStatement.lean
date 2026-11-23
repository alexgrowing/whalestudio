import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralEqZeroOfNormalisedCosetIntegrals
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientIntegral_eq_zero_of_normalised_coset_integrals : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (T N : Subgroup H), IsClosed (T : Set H) → IsClosed (N : Set H) → IsMulCommutative T → (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) → Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2) → ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (dn : Measure N) [dn.IsHaarMeasure] [dn.IsMulRightInvariant] (φ : H → ℂ), Measurable φ → LeftInv T φ → Integrable (descend T φ) (quotMeas T dt dh) → (∀ x, ∫ n : N, φ (n * x) ∂dn = 0) → quotInt T dt dh φ = 0 := by
  first | exact @GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero | exact GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero | (intros; apply GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero <;> assumption)
