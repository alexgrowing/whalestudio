import Mathlib
import GroundTheory.AutomorphicForms.TraceFormulaCompact

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

theorem ccToL1_add (f g : CompactlySupportedContinuousMap G ℂ) :
    ccToL1 μ (f + g) = ccToL1 μ f + ccToL1 μ g := by
  unfold ccToL1
  rw [← MemLp.toLp_add]
  rfl

theorem ccToL1_zero : ccToL1 μ (0 : CompactlySupportedContinuousMap G ℂ) = 0 := by
  unfold ccToL1
  exact MemLp.toLp_zero _

theorem ccToL1_sum {ι : Type*} (s : Finset ι) (f : ι → CompactlySupportedContinuousMap G ℂ) :
    ccToL1 μ (∑ i ∈ s, f i) = ∑ i ∈ s, ccToL1 μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ccToL1_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ccToL1_add, ih]

end UnitaryRep

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isTraceClass_integrated_sum_conv {ι : Type*} (s : Finset ι)
    (φ ψ : ι → CompactlySupportedContinuousMap G ℂ) :
    IsTraceClass ((rightRegularRep Γ μ).integrated μ
      (UnitaryRep.ccToL1 μ (∑ i ∈ s, conv μ (φ i) (ψ i)))) := by
  classical
  rw [UnitaryRep.ccToL1_sum, map_sum]
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, isTraceClass_iff, traceNorm_zero]
    exact ENNReal.zero_lt_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (isTraceClass_integrated_conv Γ μ (φ a) (ψ a)).add ih

theorem traceFormula_sum_conv {ι : Type*} (t : Finset ι)
    (φ ψ : ι → CompactlySupportedContinuousMap G ℂ) (f : CompactlySupportedContinuousMap G ℂ)
    (hf : f = ∑ i ∈ t, conv μ (φ i) (ψ i))
    {s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))}
    [∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))]
    (hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V)
    (hsum : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
      fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ)
    (hirr : ∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible)
    (r : ConjClasses Γ → Γ) (hr : ∀ c, ConjClasses.mk (r c) = c)
    (ν : ∀ c : ConjClasses Γ, Measure (Subgroup.centralizer {((r c : Γ) : G)}))
    (hν : ∀ c, (ν c).IsHaarMeasure)
    (ρ : ∀ c : ConjClasses Γ, Measure (RightCosetSpace (Subgroup.centralizer {((r c : Γ) : G)})))
    (hρ : ∀ c, IsWeilMeasure (Subgroup.centralizer {((r c : Γ) : G)}) μ (ν c) (ρ c)) :
    HasSum (fun π : Quotient (UnitaryRep.restrictSetoid (rightRegularRep Γ μ) hinv) =>
        (UnitaryRep.multiplicity (rightRegularRep Γ μ) hinv π : ℂ) *
          trace (((rightRegularRep Γ μ).restrict π.out (hinv π.out)).integrated μ
            (UnitaryRep.ccToL1 μ f)))
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    HasSum (fun c : ConjClasses Γ =>
        (quotientMeasure (centralizerLattice Γ ((r c : Γ) : G)) (ν c) univ).toReal •
          ∫ y, conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f y ∂ρ c)
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    ∀ c, Integrable (conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f) (ρ c) := by
  subst hf
  exact traceFormula Γ μ _ (isTraceClass_integrated_sum_conv Γ μ t φ ψ) hinv hsum hirr r hr ν hν
    ρ hρ

end RightCosetSpace

end

end GroundTheory.Automorphic
