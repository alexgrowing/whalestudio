import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary

noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal ENNReal Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Height

variable {D : D7} (V : HSp D)

theorem isCompact_setOf_height_le (C : ℝ) : IsCompact {g : GA D V | height V g ≤ C} := by
  refine (GlobalTheory.AdelicU.isCompact_height_le (F := D.host.F) D.sp.cm.sig V.gram C.toNNReal).of_isClosed_subset
    (isClosed_le (continuous_height V) continuous_const) fun g hg => ?_
  exact NNReal.le_toNNReal_of_coe_le hg

variable {X : Type} [NormedAddCommGroup X]

end Height

section Quot

variable {G : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [BorelSpace G] [LocallyCompactSpace G] [T2Space G] {R : Subgroup G} {μR : Measure R} {μG : Measure G} [SFinite μG]
  [μG.IsMulLeftInvariant] [μR.IsHaarMeasure] [μR.IsInvInvariant]

end Quot

theorem quotientIntegral_trivial_count {G : Type} [Group G] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (f : G → ℂ) : IsQuotIntL1 (R := ⊥) (Measure.dirac 1) Measure.count f (∑ g, f g) := by
  rw [isQuotIntL1_bot]
  refine ⟨Integrable.of_finite, ?_⟩
  rw [integral_fintype]
  · simp
  · exact Integrable.of_finite

example : let _ : MeasurableSpace (Multiplicative (ZMod 2)) := ⊤
    IsQuotIntL1 (R := (⊥ : Subgroup (Multiplicative (ZMod 2)))) (Measure.dirac 1) Measure.count (fun _ => (1 : ℂ)) 2 := by
  let _ : MeasurableSpace (Multiplicative (ZMod 2)) := ⊤
  have : MeasurableSingletonClass (Multiplicative (ZMod 2)) := ⟨fun _ => trivial⟩
  convert quotientIntegral_trivial_count (G := Multiplicative (ZMod 2)) fun _ => (1 : ℂ)
  simp

end GlobalTheory.Grow
