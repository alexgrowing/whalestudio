import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicFlow

theorem map_eq_smul_of_scale {V W G : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [LocallyCompactSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G]
    (Φ : G ≃ₜ+ V × W) (φ : G → G) (t : ℝ) (ht : t ≠ 0)
    (h : ∀ x, Φ (φ x) = (t • (Φ x).1, (Φ x).2))
    (μ : Measure G) [μ.IsAddHaarMeasure] :
    μ.map φ = ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| • μ := by
  set k := ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| with hk
  have hΦ : Measurable Φ := Φ.continuous.measurable
  have hΦs : Measurable Φ.symm := Φ.symm.continuous.measurable
  let ν : Measure V := Measure.addHaar
  let ρ : Measure W := Measure.addHaar
  let ψ : V × W → V × W := Prod.map (fun v => t • v) id
  have hψ : Measurable ψ := (measurable_const_smul t).prodMap measurable_id
  haveI : (μ.map Φ).IsAddHaarMeasure := Φ.isAddHaarMeasure_map μ
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map Φ) (ν.prod ρ)
  set c := Measure.addHaarScalarFactor (μ.map Φ) (ν.prod ρ) with hcdef
  have hπ : (μ.map Φ).map ψ = k • μ.map Φ := by
    have h1 : (ν.prod ρ).map ψ = k • ν.prod ρ := by
      have := Measure.map_prod_map ν ρ (f := fun v : V => t • v) (g := (id : W → W))
        (measurable_const_smul t) measurable_id
      rw [show (ν.prod ρ).map ψ = (ν.map fun v => t • v).prod (ρ.map id) from this.symm,
        Measure.map_addHaar_smul ν ht, Measure.map_id, Measure.prod_smul_left]
    rw [hc, Measure.map_smul, h1, smul_comm]
  have hφ : φ = Φ.symm ∘ ψ ∘ Φ := by
    funext x
    apply Φ.injective
    simp [h]
    rfl
  have hμ : (μ.map Φ).map Φ.symm = μ := by
    rw [Measure.map_map hΦs hΦ]
    simp
  calc μ.map φ = ((μ.map Φ).map ψ).map Φ.symm := by
        rw [Measure.map_map hΦs hψ, Measure.map_map (hΦs.comp hψ) hΦ, hφ]; rfl
    _ = k • μ := by rw [hπ, Measure.map_smul, hμ]

section Adelic

variable (F : Type) [Field F] [NumberField F]

noncomputable def coords [IsTotallyReal F] (ι : Type) :
    (ι → AdeleRing (𝓞 F) F) ≃ₜ+
      (ι → InfinitePlace F → ℝ) × (ι → FiniteAdeleRing (𝓞 F) F) where
  toFun x := (fun i w => InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w) ((x i).1 w), fun i => (x i).2)
  invFun p := fun i => (show AdeleRing (𝓞 F) F from
    (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w)).symm (p.1 i w), p.2 i))
  left_inv x := by
    funext i
    refine Prod.ext ?_ rfl
    funext w
    exact RingEquiv.symm_apply_apply _ _
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i w
    exact RingEquiv.apply_symm_apply _ _
  map_add' x y := by
    refine Prod.ext ?_ rfl
    funext i w
    exact map_add (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)) _ _
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi fun i => continuous_pi fun w => ?_)
      (continuous_pi fun i => ?_)
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).continuous.comp
        ((continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))
    · exact continuous_snd.comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i => Continuous.prodMk (continuous_pi fun w => ?_) ?_
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).symm.continuous.comp
        ((continuous_apply w).comp ((continuous_apply i).comp continuous_fst))
    · exact (continuous_apply i).comp continuous_snd

theorem coord_theta [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (t : ℝ)
    (w : InfinitePlace F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) (θ t w) = t := by
  have h : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) :
      w.Completion →+* ℝ).comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ))
      = RingHom.id ℝ := Subsingleton.elim _ _
  exact DFunLike.congr_fun h t

theorem card_places [IsTotallyReal F] :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

end Adelic

theorem map_scalar : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
    ∀ [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (ι : Type)
      [Fintype ι] (μ : Measure (ι → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (t : ℝ), 0 < t →
      μ.map (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) =
        ENNReal.ofReal ((t ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • μ := by
  intro F _ _ hF θ _ _ _ ι _ μ _ t ht
  haveI := hF
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have key := map_eq_smul_of_scale (coords F ι)
    (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) t ht.ne' ?_ μ
  · have hd : Module.finrank ℝ (ι → InfinitePlace F → ℝ) =
        Module.finrank ℚ F * Fintype.card ι := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_fintype_fun_eq_card, card_places F, mul_comm]
    rw [key, hd, abs_of_pos (inv_pos.2 (pow_pos ht _))]
  · intro x
    refine Prod.ext ?_ ?_
    · funext i w
      show InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
        (θ t w * (x i).1 w) = t * _
      rw [map_mul, coord_theta]
      rfl
    · funext i
      exact one_mul _

end GlobalTheory.CompanionTheory.AdelicFlow
