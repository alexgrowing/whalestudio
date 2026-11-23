import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

open MeasureTheory Metric Set Filter Real
open scoped ENNReal Topology Pointwise

namespace GlobalTheory

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨circleMap 0 1 θ • (x : E), by simp [norm_smul]⟩

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem coe_sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) :
    (sphereRotation θ x : E) = circleMap 0 1 θ • (x : E) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_sphereRotation :
    Continuous (Function.uncurry (sphereRotation (E := E))) := by
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ Function.uncurry (sphereRotation (E := E))) =
      fun q : ℝ × sphere (0 : E) 1 => circleMap 0 1 q.1 • (q.2 : E) := by
    funext q
    exact coe_sphereRotation q.1 q.2
  rw [e]
  exact ((continuous_circleMap 0 1).comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem measurePreserving_sphereRotation [FiniteDimensional ℂ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (θ : ℝ) :
    MeasurePreserving (sphereRotation θ) μ.toSphere μ.toSphere := by
  set ζ : ℂ := circleMap 0 1 θ with hζ_def
  have hζ : ‖ζ‖ = 1 := by simp [ζ, norm_circleMap_zero]
  have hζ0 : ζ ≠ 0 := by
    rw [← norm_ne_zero_iff, hζ]; exact one_ne_zero
  have hm : Measurable (sphereRotation (E := E) θ) :=
    (continuous_sphereRotation.comp (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hm, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' μ (hm hs), Measure.toSphere_apply' μ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • ((↑) '' (sphereRotation θ ⁻¹' s) : Set E) =
      (fun v : E => ζ • v) ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext v
    constructor
    · rintro ⟨t, ht, _, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨sphereRotation θ w, hw, rfl⟩, ?_⟩
      show t • ((sphereRotation θ w : sphere (0 : E) 1) : E) = ζ • (t • (w : E))
      rw [coe_sphereRotation]
      exact smul_comm t ζ (w : E)
    · rintro ⟨t, ht, _, ⟨u, hu, rfl⟩, huv⟩
      have hwmem : ζ⁻¹ • (u : E) ∈ sphere (0 : E) 1 := by
        simp [norm_smul, hζ]
      set w : sphere (0 : E) 1 := ⟨ζ⁻¹ • (u : E), hwmem⟩ with hw_def
      have hw : sphereRotation θ w = u := by
        apply Subtype.ext
        rw [coe_sphereRotation]
        show ζ • ζ⁻¹ • (u : E) = u
        rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul]
      refine ⟨t, ht, _, ⟨w, ?_, rfl⟩, ?_⟩
      · show sphereRotation θ w ∈ s
        rw [hw]; exact hu
      · have huv' : t • (u : E) = ζ • v := huv
        show t • (ζ⁻¹ • (u : E)) = v
        rw [smul_comm t ζ⁻¹, huv', smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  rw [hset]
  exact (measurePreserving_smul_of_norm_eq_one μ hζ).measure_preimage_emb
    (MeasurableEquiv.smul₀ ζ hζ0).measurableEmbedding _

end Rotation

section Torus

variable {ι : Type*} [Fintype ι]

end Torus

section Concavity

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

end Concavity

end GlobalTheory
