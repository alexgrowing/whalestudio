import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF

open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped NNReal ENNReal

namespace GlobalTheory.ModularAutomorphism

section Group

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem smul_haar_cancel (ρ : Measure H) [ρ.IsHaarMeasure] {c d : ℝ≥0} (h : c • ρ = d • ρ) : c = d := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have h0 : ρ K ≠ 0 := (measure_pos_of_mem_nhds ρ hK1).ne'
  have h1 : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have h2 : (c : ℝ≥0∞) * ρ K = (d : ℝ≥0∞) * ρ K := by
    have := congrArg (fun τ : Measure H => τ K) h
    exact this
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 h2)

theorem map_right_eq (ρ : Measure H) [ρ.IsHaarMeasure] (g : H) :
    ρ.map (· * g) = modularCharacterFun g • ρ := by
  rw [modularCharacterFun_eq_haarScalarFactor ρ g]
  exact isMulLeftInvariant_eq_smul _ ρ

theorem modular_aut (φ : H ≃ₜ* H) (g : H) : modularCharacterFun (φ g) = modularCharacterFun g := by
  let ρ : Measure H := Measure.haar
  have hφ : Measurable φ := φ.continuous.measurable
  haveI : (ρ.map φ).IsHaarMeasure := φ.toMulEquiv.isHaarMeasure_map ρ φ.continuous φ.symm.continuous
  apply smul_haar_cancel (ρ.map φ)
  rw [← map_right_eq, ← Measure.map_smul, ← map_right_eq, map_map (measurable_mul_const _) hφ,
    map_map hφ (measurable_mul_const _)]
  congr 1
  funext x
  simp

theorem continuous_modular : Continuous fun g : H => (modularCharacterFun g : ℝ) := by
  let ρ : Measure H := Measure.haar
  obtain ⟨f, hfc, hf0, hf1⟩ := exists_continuous_nonneg_pos (1 : H)
  have hI : ∫ x, f x ∂ρ ≠ 0 :=
    ne_of_gt (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hf1)
  have hc : Continuous fun x : H => ∫ y, f (y⁻¹ * x) ∂ρ.inv :=
    continuous_integral_apply_inv_mul f.continuous hfc
  have he : ∀ g : H, (modularCharacterFun g : ℝ) = (∫ y, f (y⁻¹ * g) ∂ρ.inv) / ∫ x, f x ∂ρ := by
    intro g
    rw [modularCharacterFun_eq_haarScalarFactor ρ g,
      haarScalarFactor_eq_integral_div _ _ f.continuous hfc hI,
      integral_map (measurable_mul_const g).aemeasurable f.continuous.aestronglyMeasurable,
      Measure.inv_def, integral_map measurable_inv.aemeasurable
        (by fun_prop : Continuous fun y : H => f (y⁻¹ * g)).aestronglyMeasurable]
    simp
  simp_rw [he]
  exact hc.div_const _

theorem map_inv_eq (ρ : Measure H) [ρ.IsHaarMeasure] [ρ.IsMulRightInvariant] : ρ.inv = ρ := by
  have h : ρ.inv = haarScalarFactor ρ.inv ρ • ρ := isMulLeftInvariant_eq_smul _ ρ
  set c := haarScalarFactor ρ.inv ρ
  have h2 : (c * c) • ρ = (1 : ℝ≥0) • ρ := by
    have h3 : ρ.inv.inv = c • ρ.inv := by
      conv_lhs => rw [h]
      rw [Measure.inv_def, Measure.map_smul, ← Measure.inv_def]
    rw [Measure.inv_inv, h, smul_smul] at h3
    rw [one_smul]
    exact h3.symm
  have h4 : c * c = 1 := smul_haar_cancel ρ h2
  have h5 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h4
    have h0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [h, h5, one_smul]

end Group

def conjAut {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G) (b : G)
    (h1 : ∀ m ∈ N, b * m * b⁻¹ ∈ N) (h2 : ∀ m ∈ N, b⁻¹ * m * b ∈ N) : N ≃ₜ* N where
  toFun m := ⟨b * m * b⁻¹, h1 m m.2⟩
  invFun m := ⟨b⁻¹ * m * b, h2 m m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

theorem unimodular_of_contracted {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G} (hν : GlobalTheory.Dec.IsHaarSub (N : Set G) ν)
    (a : ℝ → G) (h1 : ∀ s : ℝ, ∀ m ∈ N, a s * m * (a s)⁻¹ ∈ N)
    (h2 : ∀ s : ℝ, ∀ m ∈ N, (a s)⁻¹ * m * a s ∈ N)
    (h3 : ∀ m ∈ N, Tendsto (fun s : ℝ => a s * m * (a s)⁻¹) atBot (nhds (1 : G))) :
    (∀ m ∈ N, ν.map (fun x : G => x * m) = ν) ∧ ν.map (fun x : G => x⁻¹) = ν := by
  obtain ⟨hne, hfin, hcar, hleft⟩ := hν
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hE : MeasurableEmbedding (Subtype.val : N → G) := MeasurableEmbedding.subtype_coe hN.measurableSet
  have hv : Measurable (Subtype.val : N → G) := hE.measurable
  let μ : Measure N := ν.comap Subtype.val
  have hμ : μ.map Subtype.val = ν := by
    rw [hE.map_comap, Subtype.range_coe_subtype]
    exact Measure.restrict_eq_self_of_ae_mem hcar
  haveI : μ.IsMulLeftInvariant := ⟨fun g => by
    apply hE.map_injective
    change (μ.map (g * ·)).map Subtype.val = μ.map Subtype.val
    have : (Subtype.val : N → G) ∘ (g * ·) = (fun x : G => (g : G) * x) ∘ Subtype.val := rfl
    rw [map_map hv (measurable_const_mul g), this, ← map_map (measurable_const_mul _) hv, hμ, hleft g g.2]⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [hE.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top⟩
  haveI : NeZero μ := ⟨fun h => hne (by rw [← hμ, h, Measure.map_zero])⟩
  haveI : TopologicalSpace.PseudoMetrizableSpace N := inferInstance
  haveI : μ.Regular := inferInstance
  haveI : μ.IsHaarMeasure := {}
  have hmod : ∀ g : N, modularCharacterFun g = 1 := by
    intro g
    have t1 : Tendsto (fun s : ℝ => conjAut N (a s) (h1 s) (h2 s) g) atBot (nhds (1 : N)) :=
      tendsto_subtype_rng.2 (h3 g g.2)
    have t2 := ((continuous_modular (H := N)).tendsto 1).comp t1
    simp only [Function.comp_def, modular_aut, modularCharacterFun_map_one] at t2
    exact_mod_cast tendsto_const_nhds_iff.1 t2
  have hr : ∀ g : N, μ.map (· * g) = μ := fun g => by rw [map_right_eq, hmod, one_smul]
  haveI : μ.IsMulRightInvariant := ⟨hr⟩
  refine ⟨fun m hm => ?_, ?_⟩
  · have : (fun x : G => x * m) ∘ (Subtype.val : N → G) = Subtype.val ∘ (· * (⟨m, hm⟩ : N)) := rfl
    conv_lhs => rw [← hμ]
    rw [map_map (measurable_mul_const m) hv, this, ← map_map hv (measurable_mul_const _), hr, hμ]
  · have : (fun x : G => x⁻¹) ∘ (Subtype.val : N → G) = Subtype.val ∘ (Inv.inv : N → N) := rfl
    conv_lhs => rw [← hμ]
    rw [map_map measurable_inv hv, this, ← map_map hv measurable_inv, ← Measure.inv_def, map_inv_eq, hμ]

end GlobalTheory.ModularAutomorphism
