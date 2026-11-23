import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CTInv

set_option synthInstance.maxHeartbeats 400000 in
theorem ct_mul_left_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d)
    (H' : Plane E d d₁) (f c : UA σ W.J → ℂ), IsCT H' f c →
    (∃ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ ∧ μ 𝓕 = 1) →
    ∀ n ∈ unip σ W H', ∀ h, c (n * h) = c h := by
  intro F E _ _ _ _ _ σ d d₁ W H' f c hc ⟨μ, 𝓕, hμ, h𝓕, h1⟩ n hn h
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (UA σ W.J) := inferInstance
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  set n' : unip σ W H' := ⟨n, hn⟩ with hn'
  let e : unip σ W H' ≃ᵐ unip σ W H' := MeasurableEquiv.mulRight n'
  let μ' : Measure (unip σ W H') := μ.map e
  haveI : μ'.IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ n'
  let 𝓕' : Set (unip σ W H') := e.symm ⁻¹' 𝓕
  have hpres : MeasurePreserving e.symm μ' μ := by
    refine ⟨e.symm.measurable, ?_⟩
    simp only [μ', Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self, Measure.map_id]
  have h𝓕' : IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕' μ' := by
    refine h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro g x
    simp [e, MeasurableEquiv.mulRight, Subgroup.smul_def, mul_assoc]
  have h1' : μ' 𝓕' = 1 := by
    simp only [μ', 𝓕', e.map_apply]
    rw [← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]; exact h1
  have A := hc μ' 𝓕' inferInstance h𝓕' h1' h
  have B := hc μ 𝓕 hμ h𝓕 h1 (n * h)
  rw [A, B, e.measurableEmbedding.setIntegral_map]
  have : e ⁻¹' 𝓕' = 𝓕 := by
    simp only [𝓕']; rw [← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]
  rw [this]
  congr 1; funext u
  show f (u.1 * (n * h)) = f ((u * n' : unip σ W H').1 * h)
  rw [Subgroup.coe_mul, mul_assoc]

end GlobalTheory.CTInv
