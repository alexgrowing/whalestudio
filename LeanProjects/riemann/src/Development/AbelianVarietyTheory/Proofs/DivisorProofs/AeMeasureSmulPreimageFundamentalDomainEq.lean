import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSetOfSmulMemEqZero
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

theorem ae_measure_slice_eq (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X]
    [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D : Set X) (hD : MeasurableSet D)
    (hDf : IsFundamentalDomain Γ D μ) (E : Set S) (hE : IsFundamentalDomain Γ E ν) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E := by
  set W₀ : Set X := {x | ¬ ∃ g : Γ, g • x ∈ D} with hW₀
  have hW₀0 : μ W₀ = 0 := ae_iff.1 hDf.ae_covers
  have h0 := ae_measure_setOf_smul_mem_eq_zero ν μ hW₀0
  have h1 : ∀ᵐ y ∂μ, ∀ p : Γ × Γ, p.1 ≠ p.2 →
      ν {s | s • y ∈ (p.1 • D ∩ p.2 • D : Set X)} = 0 := by
    rw [ae_all_iff]
    intro p
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun y h => absurd hp h
    · filter_upwards [ae_measure_setOf_smul_mem_eq_zero ν μ (hDf.aedisjoint hp)] with y hy
      exact fun _ => hy
  filter_upwards [h0, h1] with y hy0 hy1
  have hU : IsFundamentalDomain Γ {s : S | s • y ∈ D} ν := by
    refine ⟨(hD.preimage (measurable_smul_const y)).nullMeasurableSet, ?_, ?_⟩
    · rw [ae_iff]
      refine measure_mono_null (fun s hs => ?_) hy0
      simp only [Set.mem_setOf_eq, not_exists] at hs ⊢
      rintro ⟨g, hg⟩
      refine hs g ?_
      simpa [Subgroup.smul_def, mul_smul] using hg
    · intro a b hab
      have key : ∀ c : Γ, ∀ s : S, s ∈ (c • {s : S | s • y ∈ D} : Set S) ↔ s • y ∈ (c • D : Set X) := by
        intro c s
        rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
        simp [Subgroup.smul_def, mul_smul]
      change ν _ = 0
      refine measure_mono_null (fun s hs => ?_) (hy1 (a, b) hab)
      exact ⟨(key a s).1 hs.1, (key b s).1 hs.2⟩
  exact hU.measure_eq hE

end GlobalTheory.CovolIndep
