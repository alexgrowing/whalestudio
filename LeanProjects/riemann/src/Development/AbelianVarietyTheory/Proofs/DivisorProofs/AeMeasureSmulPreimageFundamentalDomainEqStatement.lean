import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSmulPreimageFundamentalDomainEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSetOfSmulMemEqZero
open MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_measure_smul_preimage_fundamentalDomain_eq : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (Γ : Subgroup S) [Countable Γ] (D : Set X), MeasurableSet D → IsFundamentalDomain Γ D μ → ∀ (E : Set S), IsFundamentalDomain Γ E ν → ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E := by
  first | exact @GlobalTheory.CovolIndep.ae_measure_slice_eq | exact GlobalTheory.CovolIndep.ae_measure_slice_eq | (intros; apply GlobalTheory.CovolIndep.ae_measure_slice_eq <;> assumption)
