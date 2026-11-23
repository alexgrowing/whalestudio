import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilOne
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.OneParam GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.RealK GlobalTheory.ThK.StepK
open MeasureTheory

namespace GlobalTheory.ThK.UnipInv

theorem isHaarMeasure_map_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (g : G) :
    (μ.map (· * g)).IsHaarMeasure := by
  have hm : Measurable (fun x : G => x * g) := (continuous_mul_const g).measurable
  have hL : (μ.map (· * g)).IsMulLeftInvariant := ⟨fun a => by
    have ha : Measurable (fun x : G => a * x) := (continuous_const_mul a).measurable
    rw [Measure.map_map ha hm]
    have : (fun x : G => a * x) ∘ (fun x : G => x * g) = (fun x : G => x * g) ∘ (fun x : G => a * x) := by
      funext x; simp [mul_assoc]
    rw [this, ← Measure.map_map hm ha, map_mul_left_eq_self]⟩
  have hF : IsFiniteMeasureOnCompacts (μ.map (· * g)) :=
    Measure.IsFiniteMeasureOnCompacts.map μ (Homeomorph.mulRight g)
  have hO : (μ.map (· * g)).IsOpenPosMeasure :=
    (continuous_mul_const g).isOpenPosMeasure_map (mul_right_surjective g)
  exact {}

theorem isFundamentalDomain_map_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) (μ : Measure G) (𝓕 : Set G)
    (h : IsFundamentalDomain Γ 𝓕 μ) (g : G) :
    IsFundamentalDomain Γ ((· * g⁻¹) ⁻¹' 𝓕) (μ.map (· * g)) := by
  have hm : ∀ g : G, Measurable (fun x : G => x * g) := fun g => (continuous_mul_const g).measurable
  have hq : Measure.QuasiMeasurePreserving (fun x : G => x * g⁻¹) (μ.map (· * g)) μ := by
    refine ⟨hm _, ?_⟩
    rw [Measure.map_map (hm _) (hm _)]
    have : (fun x : G => x * g⁻¹) ∘ (fun x : G => x * g) = id := by
      funext x; simp
    rw [this, Measure.map_id]
  refine h.preimage_of_equiv hq (e := id) Function.bijective_id ?_
  intro γ x
  simp [Subgroup.smul_def, mul_assoc]

theorem setIntegral_map_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (𝓕 : Set G) (g : G) (φ : G → ℂ) :
    ∫ v in (· * g⁻¹) ⁻¹' 𝓕, φ v ∂(μ.map (· * g)) = ∫ x in 𝓕, φ (x * g) ∂μ := by
  have := setIntegral_map_equiv (μ := μ) (Homeomorph.mulRight g).toMeasurableEquiv φ ((· * g⁻¹) ⁻¹' 𝓕)
  have h2 : (Homeomorph.mulRight g).toMeasurableEquiv ⁻¹' ((· * g⁻¹) ⁻¹' 𝓕) = 𝓕 := by
    ext x; simp
  rw [h2] at this
  simpa using this

theorem map_mul_right_apply {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (𝓕 : Set G) (g : G) :
    (μ.map (· * g)) ((· * g⁻¹) ⁻¹' 𝓕) = μ 𝓕 := by
  have := (Homeomorph.mulRight g).toMeasurableEquiv.map_apply (μ := μ) ((· * g⁻¹) ⁻¹' 𝓕)
  have h2 : (Homeomorph.mulRight g).toMeasurableEquiv ⁻¹' ((· * g⁻¹) ⁻¹' 𝓕) = 𝓕 := by
    ext x; simp
  rw [h2] at this
  simpa using this

theorem average_mul_left {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (U Γ : Subgroup G) (μ : Measure U) (𝓕 : Set U) (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (Γ.subgroupOf U) 𝓕 μ) (h1 : μ 𝓕 = 1) (f c : G → ℂ)
    (hc : ∀ (μ : Measure U) (𝓕 : Set U), μ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf U) 𝓕 μ → μ 𝓕 = 1 →
      ∀ h, c h = ∫ u in 𝓕, f (u.1 * h) ∂μ) (u : G) (hu : u ∈ U) (h : G) : c (u * h) = c h := by
  have A := hc μ 𝓕 hμ hF h1 (u * h)
  have B := hc (μ.map (· * (⟨u, hu⟩ : U))) ((· * (⟨u, hu⟩ : U)⁻¹) ⁻¹' 𝓕)
    (isHaarMeasure_map_mul_right μ _) (isFundamentalDomain_map_mul_right _ μ 𝓕 hF _)
    ((map_mul_right_apply μ 𝓕 _).trans h1) h
  rw [A, B, setIntegral_map_mul_right μ 𝓕 _ (fun v : U => f (v.1 * h))]
  simp [mul_assoc]

theorem isCT_unip_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ} {Y : Spc F E n} {H : Plane E n n₁}, (∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧ IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1) →
    ∀ {f c : UA σ Y.J → ℂ}, IsCT (W := Y) H f c → ∀ u ∈ unip σ Y H, ∀ h, c (u * h) = c h := by
  intro F E _ _ _ _ _ σ n n₁ Y H ⟨μ, 𝓕, hμ, hF, h1⟩ f c hc u hu h
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (UA σ Y.J) := inferInstance
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  exact average_mul_left (unip σ Y H) (ratU σ Y.J) μ 𝓕 hμ hF h1 f c hc u hu h

end GlobalTheory.ThK.UnipInv
