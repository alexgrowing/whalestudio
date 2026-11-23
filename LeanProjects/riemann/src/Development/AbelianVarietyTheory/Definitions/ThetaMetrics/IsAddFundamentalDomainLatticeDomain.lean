import Mathlib

open MeasureTheory Module Submodule Set

namespace GlobalTheory

noncomputable section

section Mean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

def latticeDomain : Set E :=
  ZSpan.fundamentalDomain ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)

theorem latticeDomain_isBounded : Bornology.IsBounded (latticeDomain L) :=
  ZSpan.fundamentalDomain_isBounded _

theorem existsUnique_add_mem_latticeDomain (x : E) : ∃! a : L, x + a ∈ latticeDomain L := by
  have h := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) x
  have hs := (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L
  obtain ⟨⟨a, ha⟩, h1, h2⟩ := h
  refine ⟨⟨a, hs ▸ ha⟩, ?_, ?_⟩
  · simpa [latticeDomain, add_comm, Submodule.vadd_def] using h1
  · rintro ⟨b, hb⟩ hb'
    have := h2 ⟨b, hs.symm ▸ hb⟩ (by simpa [latticeDomain, add_comm, Submodule.vadd_def] using hb')
    exact Subtype.ext (by simpa using this)

section Measure

variable [MeasurableSpace E] [BorelSpace E]

theorem measurableSet_latticeDomain : MeasurableSet (latticeDomain L) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem isAddFundamentalDomain_latticeDomain (μ : Measure E) :
    IsAddFundamentalDomain L (latticeDomain L) μ :=
  ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) μ

theorem measure_latticeDomain (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (latticeDomain L) = ENNReal.ofReal (ZLattice.covolume L μ) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain_latticeDomain L μ),
    ofReal_measureReal (latticeDomain_isBounded L).measure_lt_top.ne]

def latticeProb : Measure E :=
  (Measure.addHaar (latticeDomain L))⁻¹ • (Measure.addHaar : Measure E).restrict (latticeDomain L)

theorem latticeProb_eq (μ : Measure E) [μ.IsAddHaarMeasure] :
    latticeProb L = (ENNReal.ofReal (ZLattice.covolume L μ))⁻¹ • μ.restrict (latticeDomain L) := by
  have h := Measure.isAddLeftInvariant_eq_smul (Measure.addHaar : Measure E) μ
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (Measure.addHaar : Measure E) μ
  set c := Measure.addHaarScalarFactor (Measure.addHaar : Measure E) μ
  rw [← measure_latticeDomain, latticeProb, h]
  have hc0 : (c : ENNReal) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Measure.restrict_smul, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_smul,
    smul_eq_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), mul_right_comm,
    ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul]

instance isProbabilityMeasure_latticeProb : IsProbabilityMeasure (latticeProb L) := by
  constructor
  rw [latticeProb, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  refine ENNReal.inv_mul_cancel ?_ (latticeDomain_isBounded L).measure_lt_top.ne
  rw [measure_latticeDomain]
  simpa using ZLattice.covolume_pos L Measure.addHaar

theorem integrable_latticeProb {f : E → G} (hf : Continuous f) : Integrable f (latticeProb L) := by
  have h0 : Measure.addHaar (latticeDomain L) ≠ 0 := by
    rw [measure_latticeDomain]
    simpa using ZLattice.covolume_pos L Measure.addHaar
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 h0)
  exact (hf.continuousOn.integrableOn_compact
    (latticeDomain_isBounded L).isCompact_closure).mono_set subset_closure

end Measure

def latticeMean (f : E → G) : G :=
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  ∫ x, f x ∂(latticeProb L)

theorem latticeMean_eq_integral [m : MeasurableSpace E] [hm : BorelSpace E] (f : E → G) :
    latticeMean L f = ∫ x, f x ∂(latticeProb L) := by
  obtain ⟨rfl⟩ := hm
  rfl

theorem latticeMean_eq_latticeDomain [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (f : E → G) :
    latticeMean L f = (ZLattice.covolume L μ)⁻¹ • ∫ x in latticeDomain L, f x ∂μ := by
  rw [latticeMean_eq_integral, latticeProb_eq L μ, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (ZLattice.covolume_pos L μ).le]

theorem latticeMean_eq [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {D : Set E} (hD : IsAddFundamentalDomain L D μ) {f : E → G}
    (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) :
    latticeMean L f = (ZLattice.covolume L μ)⁻¹ • ∫ x in D, f x ∂μ := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  rw [latticeMean_eq_latticeDomain L μ,
    (isAddFundamentalDomain_latticeDomain L μ).setIntegral_eq hD]
  rintro ⟨a, ha⟩ x
  simpa [Submodule.vadd_def, add_comm] using hf a ha x

@[simp] theorem latticeMean_const [CompleteSpace G] (c : G) :
    latticeMean L (fun _ => c) = c := by
  borelize E
  simp [latticeMean_eq_integral]

theorem latticeMean_finset_sum {ι : Type*} (s : Finset ι) {f : ι → E → G}
    (hf : ∀ i ∈ s, Continuous (f i)) :
    latticeMean L (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, latticeMean L (f i) := by
  borelize E
  simp only [latticeMean_eq_integral]
  exact integral_finset_sum s fun i hi => integrable_latticeProb L (hf i hi)

theorem latticeMean_const_mul {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) (f : E → 𝕜) :
    latticeMean L (fun x => c * f x) = c * latticeMean L f := by
  borelize E
  simp only [latticeMean_eq_integral]
  exact integral_const_mul c f

theorem latticeMean_nonneg {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ latticeMean L f := by
  borelize E
  simp only [latticeMean_eq_integral]
  exact integral_nonneg hf

theorem latticeMean_comp_add {f : E → G} (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) (w : E) :
    latticeMean L (fun x => f (x + w)) = latticeMean L f := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have hD : IsAddFundamentalDomain L ((fun x => x + w) ⁻¹' latticeDomain L) μ := by
    refine IsAddFundamentalDomain.mk'
      ((measurable_add_const w) (measurableSet_latticeDomain L)).nullMeasurableSet fun x => ?_
    have := existsUnique_add_mem_latticeDomain L (x + w)
    simpa [Submodule.vadd_def, add_comm, add_left_comm, add_assoc] using this
  rw [latticeMean_eq L μ hD (f := fun x => f (x + w))
    (fun a ha x => by simpa [add_right_comm] using hf a ha (x + w)),
    latticeMean_eq_latticeDomain L μ]
  congr 1
  exact (measurePreserving_add_right μ w).setIntegral_preimage_emb
    (measurableEmbedding_addRight w) f _

theorem eq_zero_of_latticeMean_eq_zero {f : E → ℝ} (hc : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) (h : latticeMean L f = 0) : f = 0 := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  rw [latticeMean_eq_integral, integral_eq_zero_iff_of_nonneg h0 (integrable_latticeProb L hc),
    latticeProb_eq L μ] at h
  have h1 : f =ᵐ[μ.restrict (latticeDomain L)] 0 :=
    (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)).1 h
  have hm : MeasurableSet {x | f x ≠ 0} :=
    (isOpen_ne_fun hc continuous_const).measurableSet
  have h2 : μ {x | f x ≠ 0} = 0 := by
    refine (isAddFundamentalDomain_latticeDomain L μ).measure_zero_of_invariant _ ?_ ?_
    · rintro ⟨a, ha⟩
      ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      have := hf (-a) (L.neg_mem ha) x
      simp only [Submodule.vadd_def, Set.mem_setOf_eq, vadd_eq_add, NegMemClass.coe_neg]
      rw [add_comm, this]
    · rw [← Measure.restrict_apply hm]
      exact h1
  exact (Continuous.ae_eq_iff_eq μ hc continuous_zero).1 h2

theorem exists_forall_le_of_periodic {f : E → ℝ} (hc : Continuous f)
    (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) : ∃ x₀, ∀ x, f x ≤ f x₀ := by
  have hK := (latticeDomain_isBounded L).isCompact_closure
  obtain ⟨a₀, ha₀, -⟩ := existsUnique_add_mem_latticeDomain L 0
  obtain ⟨x₀, -, hx₀⟩ := hK.exists_isMaxOn ⟨_, subset_closure ha₀⟩ hc.continuousOn
  refine ⟨x₀, fun x => ?_⟩
  obtain ⟨a, ha, -⟩ := existsUnique_add_mem_latticeDomain L x
  rw [← hf a a.2 x]
  exact hx₀ (subset_closure ha)

theorem latticeMean_eq_of_periodic (L' : Submodule ℤ E) [DiscreteTopology L'] [IsZLattice ℝ L']
    [CompleteSpace G] {f : E → G} (hc : Continuous f) (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x)
    (hf' : ∀ a ∈ L', ∀ x, f (x + a) = f x) : latticeMean L f = latticeMean L' f := by
  borelize E
  obtain ⟨x₀, hx₀⟩ := exists_forall_le_of_periodic L hc.norm (fun a ha x => by rw [hf a ha x])
  have hi : Integrable (Function.uncurry fun x y : E => f (x + y))
      ((latticeProb L).prod (latticeProb L')) :=
    Integrable.of_bound (hc.comp continuous_add).aestronglyMeasurable ‖f x₀‖
      (ae_of_all _ fun p => hx₀ _)
  have h := integral_integral_swap hi
  simp only [← latticeMean_eq_integral] at h
  have h1 : ∀ x, latticeMean L' (fun y => f (x + y)) = latticeMean L' f := fun x => by
    simpa only [add_comm x] using latticeMean_comp_add L' hf' x
  simp only [h1, latticeMean_comp_add L hf, latticeMean_const] at h
  exact h.symm

theorem latticeMean_comp_equiv {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] (L' : Submodule ℤ E') [DiscreteTopology L'] [IsZLattice ℝ L']
    (e : E ≃L[ℝ] E') (he : ∀ x, e x ∈ L' ↔ x ∈ L) {f : E' → G}
    (hf : ∀ a ∈ L', ∀ x, f (x + a) = f x) :
    latticeMean L (fun x => f (e x)) = latticeMean L' f := by
  borelize E E'
  set μ : Measure E := Measure.addHaar
  have hmp : MeasurePreserving e μ (μ.map e) := ⟨e.continuous.measurable, rfl⟩
  have hD : IsAddFundamentalDomain L (e ⁻¹' latticeDomain L') μ := by
    refine IsAddFundamentalDomain.mk'
      (e.continuous.measurable (measurableSet_latticeDomain L')).nullMeasurableSet fun x => ?_
    obtain ⟨a, ha, hu⟩ := existsUnique_add_mem_latticeDomain L' (e x)
    refine ⟨⟨e.symm a, (he _).1 (by simp)⟩, ?_, ?_⟩
    · simpa [Submodule.vadd_def, add_comm] using ha
    · rintro ⟨b, hb⟩ hb'
      have := hu ⟨e b, (he _).2 hb⟩ (by simpa [Submodule.vadd_def, add_comm] using hb')
      apply Subtype.ext
      simp [← this]
  rw [latticeMean_eq L μ hD (f := fun x => f (e x))
    (fun a ha x => by simpa using hf (e a) ((he _).2 ha) (e x)),
    latticeMean_eq_latticeDomain L' (μ.map e),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ hD,
    ZLattice.covolume_eq_measure_fundamentalDomain L' (μ.map e)
      (isAddFundamentalDomain_latticeDomain L' _),
    ← hmp.measureReal_preimage (measurableSet_latticeDomain L').nullMeasurableSet]
  congr 1
  exact hmp.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding f _

end Mean

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] (L : ∀ i, Submodule ℤ (E i))

instance discreteTopology_submodulePi [∀ i, DiscreteTopology (L i)] :
    DiscreteTopology (Submodule.pi Set.univ L) :=
  DiscreteTopology.of_continuous_injective
    (f := fun (x : Submodule.pi Set.univ L) (i : ι) => (⟨x.1 i, x.2 i trivial⟩ : L i))
    (continuous_pi fun i => ((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
    (fun x y h => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i)))

instance isZLattice_submodulePi [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)] :
    IsZLattice ℝ (Submodule.pi Set.univ L) where
  span_top := by
    classical
    rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hx : x i ∈ span ℝ (L i : Set (E i)) := by rw [IsZLattice.span_top]; trivial
    refine span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span (LinearMap.single ℝ E i) hx)
    rintro _ ⟨a, ha, rfl⟩ j -
    by_cases h : j = i
    · subst h; simpa using ha
    · simp [Pi.single_eq_of_ne h]

def piLpLattice : Submodule ℤ (PiLp 2 E) :=
  ZLattice.comap ℝ (Submodule.pi Set.univ L) (PiLp.continuousLinearEquiv 2 ℝ E).toLinearMap

@[simp] theorem mem_piLpLattice {x : PiLp 2 E} : x ∈ piLpLattice L ↔ ∀ i, x i ∈ L i :=
  ⟨fun h i => h i trivial, fun h i _ => h i⟩

instance discreteTopology_piLpLattice [∀ i, DiscreteTopology (L i)] :
    DiscreteTopology (piLpLattice L) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (Submodule.pi Set.univ L)
    (PiLp.continuousLinearEquiv 2 ℝ E).toLinearMap))

instance isZLattice_piLpLattice [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)] :
    IsZLattice ℝ (piLpLattice L) :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (Submodule.pi Set.univ L)
    (PiLp.continuousLinearEquiv 2 ℝ E).toLinearMap))

end Pi

section Prod

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] (L : Submodule ℤ E) (L' : Submodule ℤ E')

instance discreteTopology_submoduleProd [DiscreteTopology L] [DiscreteTopology L'] :
    DiscreteTopology (L.prod L') :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : L.prod L' => ((⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) : L × L'))
    (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
    (fun x y h => Subtype.ext (Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
      (congrArg Subtype.val (congrArg Prod.snd h))))

instance isZLattice_submoduleProd [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L]
    [IsZLattice ℝ L'] : IsZLattice ℝ (L.prod L') where
  span_top := by
    rw [Submodule.prod_coe, Submodule.span_prod_eq ℝ L.zero_mem L'.zero_mem,
      IsZLattice.span_top, IsZLattice.span_top, Submodule.prod_top]

def prodLpLattice : Submodule ℤ (WithLp 2 (E × E')) :=
  ZLattice.comap ℝ (L.prod L') (WithLp.prodContinuousLinearEquiv 2 ℝ E E').toLinearMap

@[simp] theorem mem_prodLpLattice {x : WithLp 2 (E × E')} :
    x ∈ prodLpLattice L L' ↔ x.fst ∈ L ∧ x.snd ∈ L' := Iff.rfl

instance discreteTopology_prodLpLattice [DiscreteTopology L] [DiscreteTopology L'] :
    DiscreteTopology (prodLpLattice L L') :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (L.prod L')
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E').toLinearMap))

instance isZLattice_prodLpLattice [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L]
    [IsZLattice ℝ L'] : IsZLattice ℝ (prodLpLattice L L') :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (L.prod L')
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E').toLinearMap))

end Prod

end

end GlobalTheory
