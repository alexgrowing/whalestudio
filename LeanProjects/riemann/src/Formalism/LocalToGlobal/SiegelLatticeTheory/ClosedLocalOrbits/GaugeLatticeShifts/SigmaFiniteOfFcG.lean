import Mathlib

noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def subOf (H : Set G) (h1 : (1 : G) ∈ H) (hm : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) (hi : ∀ x ∈ H, x⁻¹ ∈ H) :
    Subgroup G where
  carrier := H
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  inv_mem' := fun {a} ha => hi a ha

theorem pull (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G) (hνc : ν (S : Set G)ᶜ = 0)
    (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) (hνf : IsFiniteMeasureOnCompacts ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (ν.comap (Subtype.val : S → G)) ∧
      (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
  have hme : MeasurableEmbedding (Subtype.val : S → G) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hmap : (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
    rw [hme.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hνc)
  refine ⟨⟨fun g => ?_⟩, ⟨fun K hK => ?_⟩, hmap⟩
  · have h1 : ((ν.comap (Subtype.val : S → G)).map (fun x => g * x)).map Subtype.val = ν := by
      rw [Measure.map_map hme.measurable (measurable_const_mul g)]
      have : (Subtype.val : S → G) ∘ (fun x : S => g * x) =
          (fun x : G => (g : G) * x) ∘ (Subtype.val : S → G) := by
        funext x; rfl
      rw [this, ← Measure.map_map (measurable_const_mul _) hme.measurable, hmap]
      exact hνi g g.2
    calc (ν.comap (Subtype.val : S → G)).map (fun x => g * x)
        = (((ν.comap (Subtype.val : S → G)).map (fun x => g * x)).map Subtype.val).comap
            Subtype.val := (hme.comap_map _).symm
      _ = ν.comap Subtype.val := by rw [h1]
  · rw [hme.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top

theorem haar_unique (S : Subgroup G) (hS : IsClosed (S : Set G)) (μ m : Measure G) (hμ0 : μ ≠ 0)
    (hμc : μ (S : Set G)ᶜ = 0) (hμi : ∀ s ∈ S, μ.map (fun x => s * x) = μ) (hμf : IsFiniteMeasureOnCompacts μ)
    (hmc : m (S : Set G)ᶜ = 0) (hmi : ∀ s ∈ S, m.map (fun x => s * x) = m) (hmf : IsFiniteMeasureOnCompacts m) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ m = c • μ := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S :=
    TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  obtain ⟨hμl, hμk, hμm⟩ := pull S hS μ hμc hμi hμf
  obtain ⟨hml, hmk, hmm⟩ := pull S hS m hmc hmi hmf
  set μ' := μ.comap (Subtype.val : S → G)
  set m' := m.comap (Subtype.val : S → G)
  have hμ := Measure.isMulLeftInvariant_eq_smul μ' (Measure.haar : Measure S)
  have hm := Measure.isMulLeftInvariant_eq_smul m' (Measure.haar : Measure S)
  set d := Measure.haarScalarFactor μ' (Measure.haar : Measure S)
  set c := Measure.haarScalarFactor m' (Measure.haar : Measure S)
  have hd : d ≠ 0 := by
    intro h0
    apply hμ0
    rw [← hμm, hμ, h0, zero_smul, Measure.map_zero]
  refine ⟨((c / d : ℝ≥0) : ℝ≥0∞), ENNReal.coe_ne_top, ?_⟩
  have hm'' : m' = (c / d) • μ' := by
    rw [hm, hμ, smul_smul, div_mul_cancel₀ c hd]
  rw [← hmm, ← hμm, hm'', Measure.map_smul]
  rfl

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore
