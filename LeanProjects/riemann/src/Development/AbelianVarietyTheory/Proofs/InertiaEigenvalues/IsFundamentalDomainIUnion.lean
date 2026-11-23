import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise Matrix

namespace GlobalTheory.ThetaUnfold

section Abstract

variable {G ι : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem lintegral_unfold (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 𝓕' : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕' : IsFundamentalDomain Δ 𝓕' μ)
    (f : G → ℝ≥0∞) (hf : ∀ δ ∈ Δ, ∀ g, f (δ * g) = f g) (hm : AEMeasurable f μ) :
    ∫⁻ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∫⁻ g in 𝓕', f g ∂μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  haveI : Countable Δ := Function.Injective.countable (f := fun δ => e (δ, (e.symm 1).2))
    fun i j h => by simpa using congrArg Prod.fst (e.injective h)
  haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : MeasurableConstSMul Δ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  haveI : SMulInvariantMeasure Δ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hset : ∀ (δ : Δ) (i : ι), (δ • (r i • 𝓕) ∩ 𝓕' : Set G) = 𝓕' ∩ e (δ, i) • 𝓕 := by
    intro δ i
    ext x
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
    rw [and_comm]
    refine and_congr_right fun _ => ?_
    rw [he]
    simp [mul_assoc]
  calc ∫⁻ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∑' i, ∫⁻ g in 𝓕, f (r i * g) ∂μ :=
        lintegral_tsum fun i => (hm.comp_quasiMeasurePreserving
          (measurePreserving_mul_left μ (r i)).quasiMeasurePreserving).restrict
    _ = ∑' i, ∫⁻ g in r i • 𝓕, f g ∂μ := by
        refine tsum_congr fun i => ?_
        rw [(measurePreserving_mul_left μ (r i)).setLIntegral_comp_emb
          (measurableEmbedding_mulLeft (r i)) f 𝓕]
        rfl
    _ = ∑' i, ∑' δ : Δ, ∫⁻ g in 𝓕' ∩ e (δ, i) • 𝓕, f g ∂μ := by
        refine tsum_congr fun i => ?_
        rw [h𝓕'.setLIntegral_eq_tsum' f (r i • 𝓕)]
        refine tsum_congr fun δ => ?_
        rw [hset]
        congr 1
        funext g
        exact hf _ (δ⁻¹).2 g
    _ = ∑' p : Δ × ι, ∫⁻ g in 𝓕' ∩ e p • 𝓕, f g ∂μ := by
        rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ = ∑' γ : Γ, ∫⁻ g in 𝓕' ∩ γ • 𝓕, f g ∂μ := e.tsum_eq (fun γ => ∫⁻ g in 𝓕' ∩ γ • 𝓕, f g ∂μ)
    _ = ∫⁻ g in 𝓕', f g ∂μ := (h𝓕.setLIntegral_eq_tsum f 𝓕').symm

theorem isFundamentalDomain_iUnion (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : IsFundamentalDomain Δ (⋃ i, r i • 𝓕) μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  have hset : ∀ (δ : Δ) (i : ι), (δ • (r i • 𝓕) : Set G) = e (δ, i) • 𝓕 := by
    intro δ i
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv]
    rw [he]
    simp [mul_assoc]
  refine ⟨.iUnion fun i => h𝓕.nullMeasurableSet.smul (r i), h𝓕.ae_covers.mono ?_, fun δ δ' hδ => ?_⟩
  · rintro x ⟨γ, hγ⟩
    refine ⟨(e.symm γ⁻¹).1⁻¹, Set.mem_iUnion.2 ⟨(e.symm γ⁻¹).2, ?_⟩⟩
    rw [← Set.mem_smul_set_iff_inv_smul_mem, hset, Prod.mk.eta, e.apply_symm_apply,
      Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγ
  · simp only [Function.onFun, Set.smul_set_iUnion, hset, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff]
    exact fun i j => h𝓕.aedisjoint fun h => hδ (by simpa using congrArg Prod.fst (e.injective h))

theorem integral_unfold {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 𝓕' : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕' : IsFundamentalDomain Δ 𝓕' μ)
    (f : G → V) (hf : ∀ δ ∈ Δ, ∀ g, f (δ * g) = f g) (hm : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ g in 𝓕, ∑' i, ‖f (r i * g)‖ₑ ∂μ ≠ ⊤) :
    (∀ᵐ g ∂μ.restrict 𝓕, Summable fun i => ‖f (r i * g)‖) ∧ IntegrableOn (fun g => ∑' i, f (r i * g)) 𝓕 μ ∧
      IntegrableOn f 𝓕' μ ∧ ∫ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∫ g in 𝓕', f g ∂μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  haveI : Countable Δ := Function.Injective.countable (f := fun δ => e (δ, (e.symm 1).2))
    fun i j h => by simpa using congrArg Prod.fst (e.injective h)
  haveI : SMulInvariantMeasure Δ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hS := isFundamentalDomain_iUnion μ Γ Δ r e he h𝓕
  have hf' : ∀ (δ : Δ) (g : G), f (δ • g) = f g := fun δ g => hf δ δ.2 g
  have hmi : ∀ i, AEStronglyMeasurable (fun g => f (r i * g)) (μ.restrict 𝓕) := fun i =>
    (hm.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (r i)).quasiMeasurePreserving).restrict
  have hI : IntegrableOn f 𝓕' μ := ⟨hm.restrict, by
    have := lintegral_unfold μ Γ Δ r e he h𝓕 h𝓕' (fun g => ‖f g‖ₑ) (fun δ h g => by rw [hf δ h]) hm.enorm
    exact lt_top_iff_ne_top.2 (this ▸ hfin)⟩
  have hr : ∀ i, (r i • 𝓕 : Set G) = e (1, i) • 𝓕 := fun i => by
    rw [Subgroup.smul_def, he]; simp
  refine ⟨?_, ⟨AEStronglyMeasurable.tsum hmi, ?_⟩, hI, ?_⟩
  · filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum fun i => (hmi i).enorm) hfin] with g hg
    have := ENNReal.summable_toReal hg.ne
    simpa using this
  · exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) hfin.lt_top
  · rw [integral_tsum hmi (by rwa [← lintegral_tsum fun i => (hmi i).enorm]), h𝓕'.setIntegral_eq hS hf',
      integral_iUnion_ae (fun i => h𝓕.nullMeasurableSet.smul (r i))
        (fun i j hij => by
          simp only [Function.onFun, hr]
          exact h𝓕.aedisjoint fun h => hij (by simpa using congrArg Prod.snd (e.injective h)))
        ((h𝓕'.integrableOn_iff hS hf').1 hI)]
    refine tsum_congr fun i => ?_
    exact ((measurePreserving_mul_left μ (r i)).setIntegral_image_emb (measurableEmbedding_mulLeft (r i)) f 𝓕).symm

end Abstract

section Concrete

open GlobalTheory.CuspRep

variable {E : Type} [Field E] {a : ℕ}

theorem exists_vecMul_eq {v ξ : Fin a → E} (hv : v ≠ 0) (hξ : ξ ≠ 0) :
    ∃ γ : GL (Fin a) E, v ᵥ* (γ : Matrix (Fin a) (Fin a) E) = ξ := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton E _ v hv).symm.trans (LinearEquiv.toSpanNonzeroSingleton E _ ξ hξ))
  have h1 := hg ⟨v, Submodule.mem_span_singleton_self v⟩
  rw [← LinearEquiv.toSpanNonzeroSingleton_one E _ v hv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one,
    LinearEquiv.toSpanNonzeroSingleton_one] at h1
  set A := LinearMap.toMatrix' g.toLinearMap
  set B := LinearMap.toMatrix' g.symm.toLinearMap
  have hAB : A * B = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  have hBA : B * A = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  refine ⟨⟨Aᵀ, Bᵀ, by rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]⟩, ?_⟩
  change v ᵥ* Aᵀ = ξ
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  first | exact h1 | exact h1.symm

variable [NumberField E]

theorem vecMul_ratGL_mul (ξ : Fin a → E) (γ : GL (Fin a) E) (g : GA E a) :
    (algebraMap E (Ad E) ∘ ξ) ᵥ* (ratGL E a γ * g).val = (algebraMap E (Ad E) ∘ (ξ ᵥ* γ.val)) ᵥ* g.val := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext j
  simp [ratGL, Matrix.vecMul, dotProduct, map_sum]

theorem ratGL_injective : Function.Injective (ratGL E a) := fun _ _ h => by
  ext i j
  exact NumberField.AdeleRing.algebraMap_injective _ E
    (congrArg (fun z : GA E a => (z : Matrix (Fin a) (Fin a) (Ad E)) i j) h)

theorem countable_range_ratGL : Countable (ratGL E a).range := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin a) (Fin a) E) := inferInstanceAs (Countable (Fin a → Fin a → E))
  haveI : Countable (GL (Fin a) E) := Units.val_injective.countable
  exact (ratGL E a).rangeRestrict_surjective.countable

theorem exists_transversal {v : Fin a → E} (hv : v ≠ 0) {P : Subgroup (GL (Fin a) E)}
    (hP : ∀ γ, γ ∈ P ↔ v ᵥ* γ.val = v) :
    ∃ (γ : {ξ : Fin a → E // ξ ≠ 0} → GL (Fin a) E) (e : P.map (ratGL E a) × {ξ : Fin a → E // ξ ≠ 0} ≃ (ratGL E a).range),
      (∀ ξ, v ᵥ* (γ ξ).val = ξ.1) ∧ ∀ p, (e p : GA E a) = p.1 * ratGL E a (γ p.2) := by
  choose γ hγ using fun ξ : {ξ : Fin a → E // ξ ≠ 0} => exists_vecMul_eq hv ξ.2
  let φ : P.map (ratGL E a) × {ξ : Fin a → E // ξ ≠ 0} → (ratGL E a).range := fun p =>
    ⟨p.1 * ratGL E a (γ p.2), mul_mem (Subgroup.map_le_range _ _ p.1.2) ⟨_, rfl⟩⟩
  refine ⟨γ, Equiv.ofBijective φ ⟨?_, ?_⟩, hγ, fun _ => rfl⟩
  · rintro ⟨⟨_, δ, hδ, rfl⟩, ξ⟩ ⟨⟨_, δ', hδ', rfl⟩, ξ'⟩ h
    have h1 : δ * γ ξ = δ' * γ ξ' := ratGL_injective (by simpa only [map_mul] using congrArg Subtype.val h)
    have h2 : ξ = ξ' := Subtype.ext (by
      have := congrArg (fun x : GL (Fin a) E => v ᵥ* x.val) h1
      simpa only [Units.val_mul, ← Matrix.vecMul_vecMul, (hP _).1 hδ, (hP _).1 hδ', hγ] using this)
    subst h2
    obtain rfl := mul_right_cancel h1
    rfl
  · rintro ⟨_, x, rfl⟩
    have h0 : v ᵥ* x.val ≠ 0 := fun h => hv (by
      have := congrArg (· ᵥ* (x⁻¹).val) h
      simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] using this)
    have h1 : x * (γ ⟨_, h0⟩)⁻¹ ∈ P := (hP _).2 (by
      have h2 : v ᵥ* (γ ⟨_, h0⟩).val = v ᵥ* x.val := hγ _
      generalize γ ⟨_, h0⟩ = y at h2 ⊢
      rw [Units.val_mul, ← Matrix.vecMul_vecMul, ← h2, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one])
    refine ⟨⟨⟨_, _, h1, rfl⟩, ⟨_, h0⟩⟩, Subtype.ext ?_⟩
    change ratGL E a _ * ratGL E a _ = _
    rw [← map_mul, inv_mul_cancel_right]

section Stabiliser

variable [MeasurableSpace (GA E a)] [MeasurableMul (GA E a)] (μ : Measure (GA E a)) [μ.IsMulLeftInvariant]
  {v : Fin a → E} (hv : v ≠ 0) {P : Subgroup (GL (Fin a) E)} (hP : ∀ γ, γ ∈ P ↔ v ᵥ* γ.val = v)
  {𝓕 𝓕' : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
  (h𝓕' : IsFundamentalDomain (P.map (ratGL E a)) 𝓕' μ)

include hv hP h𝓕 h𝓕'

theorem lintegral_tsum_vecMul (F : GA E a → (Fin a → Ad E) → ℝ≥0∞) (hF : ∀ γ g y, F (ratGL E a γ * g) y = F g y)
    (hm : AEMeasurable (fun g : GA E a => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) μ) :
    ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
      ∫⁻ g in 𝓕', F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val) ∂μ := by
  haveI := countable_range_ratGL (E := E) (a := a)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal hv hP
  have := lintegral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕' _
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [vecMul_ratGL_mul, hF, (hP _).1 hδ]) hm
  simpa only [vecMul_ratGL_mul, hF, hγ] using this

theorem integral_tsum_vecMul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : GA E a → (Fin a → Ad E) → V) (hF : ∀ γ g y, F (ratGL E a γ * g) y = F g y)
    (hm : AEStronglyMeasurable (fun g : GA E a => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) μ)
    (hfin : ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ ≠ ⊤) :
    (∀ᵐ g ∂μ.restrict 𝓕, Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖) ∧
    IntegrableOn (fun g => ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)) 𝓕 μ ∧
    IntegrableOn (fun g => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) 𝓕' μ ∧
    ∫ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
      ∫ g in 𝓕', F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val) ∂μ := by
  haveI := countable_range_ratGL (E := E) (a := a)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal hv hP
  have := integral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕' _
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [vecMul_ratGL_mul, hF, (hP _).1 hδ]) hm
    (by simpa only [vecMul_ratGL_mul, hF, hγ] using hfin)
  simpa only [vecMul_ratGL_mul, hF, hγ] using this

end Stabiliser

theorem continuous_vecMul (y : Fin a → Ad E) : Continuous fun g : GA E a => y ᵥ* g.val :=
  continuous_const.matrix_vecMul Units.continuous_val

end Concrete

end GlobalTheory.ThetaUnfold
