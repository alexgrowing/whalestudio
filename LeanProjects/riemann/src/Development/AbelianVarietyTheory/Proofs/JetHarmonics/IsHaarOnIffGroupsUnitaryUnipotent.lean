import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.HaarNotions

open Formalism.FourierDecayAlt.P.B2x1 in

theorem finite_compact_of_sigmaFinite {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) [SigmaFinite μ] (hc : μ Uᶜ = 0)
    (hl : ∀ a ∈ U, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) (K : Set (Formalism.QuantumDeterminants.Mt k r)) (hK : IsCompact K) : μ K < ∞ := by
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ hl
  have : SigmaFinite (pull hU μ) := by
    have h : SigmaFinite ((pull hU μ).map inc) := by rw [map_pull μ hc]; infer_instance
    exact SigmaFinite.of_map _ inc_memb.measurable.aemeasurable h
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Gp U hU)) := inferInstance
  have huniq := Measure.haarMeasure_unique (pull hU μ) K₀
  have hfin : pull hU μ K₀ ≠ ∞ := by
    intro hinf
    rw [hinf] at huniq
    have hzero : ∀ n, Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) = 0 := by
      intro n
      by_contra hne
      have h1 := measure_spanningSets_lt_top (pull hU μ) n
      have h2 : pull hU μ (spanningSets (pull hU μ) n) =
          ∞ * Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) :=
        congrArg (fun m : Measure (Gp U hU) => m (spanningSets (pull hU μ) n)) huniq
      rw [h2, ENNReal.top_mul hne] at h1
      exact lt_irrefl _ h1
    have huniv : Measure.haarMeasure K₀ Set.univ = 0 := by
      rw [← iUnion_spanningSets (pull hU μ)]
      exact measure_iUnion_null hzero
    have h1 : Measure.haarMeasure K₀ K₀ = 0 := measure_mono_null (Set.subset_univ _) huniv
    rw [Measure.haarMeasure_self] at h1
    exact one_ne_zero h1
  have hK' : IsCompact ((inc : Gp U hU → Formalism.QuantumDeterminants.Mt k r) ⁻¹' K) := inc_closedEmb.isCompact_preimage hK
  have h3 : pull hU μ (inc ⁻¹' K) = pull hU μ K₀ * Measure.haarMeasure K₀ (inc ⁻¹' K) :=
    congrArg (fun m : Measure (Gp U hU) => m (inc ⁻¹' K)) huniq
  rw [← map_pull (hU := hU) μ hc, inc_memb.map_apply, h3]
  exact ENNReal.mul_lt_top hfin.lt_top hK'.measure_lt_top

theorem isHaarOn_iff {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (hex : ∃ ν : Measure (Formalism.QuantumDeterminants.Mt k r), B.IsHaarOn U ν) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) :
    PI.BesselPeriodGGP.IsHaarOn U μ ↔ B.IsHaarOn U μ := by
  constructor
  · rintro ⟨hσ, h0, hc, hl⟩
    obtain ⟨ν, hν⟩ := hex
    have hfin := finite_compact_of_sigmaFinite hU μ hc hl
    obtain ⟨c, hcν⟩ := P.haar_measure_unique_up_to_scalar k r U ν μ hU hν hc hl hfin
    refine { ne_zero := h0, conc := hc, left := hl, right := ?_, finite_compact := hfin }
    intro a ha
    rw [hcν, Measure.map_smul, hν.right a ha]
  · intro h
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem isHaarOn_iff_groups : ∀ (k r : ℕ) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)), (PI.BesselPeriodGGP.IsHaarOn (GG k r) μ ↔ B.IsHaarOn (GG k r) μ) ∧ (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) ∧ ∀ z, Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → 1 ≤ k → (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ) :=
  fun k r μ =>
    ⟨isHaarOn_iff (P.unitary_group_closed k r) (P.unitary_group_haar_exists k r) μ,
      isHaarOn_iff (P.unipotent_radical_closed k r) (P.unipotent_haar_exists k r) μ,
      fun z hz hT _ => isHaarOn_iff (P.weyl_subgroup_closed k r z) (P.weyl_haar_exists k r z hz hT) μ⟩

end GlobalTheory.HaarNotions
