import Mathlib

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory

section Haar

variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

noncomputable def haarProb : Measure K := haarMeasure ⊤

instance haarProb_isHaarMeasure : (haarProb K).IsHaarMeasure := by
  unfold haarProb; infer_instance

instance haarProb_isProbabilityMeasure : IsProbabilityMeasure (haarProb K) :=
  ⟨by simpa [haarProb] using (haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K)))⟩

variable {K}

theorem eq_haarProb (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    μ = haarProb K :=
  isHaarMeasure_eq_of_isProbabilityMeasure _ _

instance haarProb_isMulRightInvariant : (haarProb K).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : IsProbabilityMeasure (Measure.map (fun x => x * g) (haarProb K)) :=
    isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact eq_haarProb _

instance haarProb_isInvInvariant : (haarProb K).IsInvInvariant := by
  refine ⟨?_⟩
  have : IsProbabilityMeasure (haarProb K).inv :=
    isProbabilityMeasure_map measurable_inv.aemeasurable
  have : (haarProb K).inv.IsHaarMeasure := {}
  exact eq_haarProb _

theorem eq_smul_haarProb (μ : Measure K) [μ.IsHaarMeasure] :
    μ = μ Set.univ • haarProb K := by
  have h := isMulInvariant_eq_smul_of_compactSpace μ (haarProb K)
  have h1 : μ Set.univ = haarScalarFactor μ (haarProb K) := by
    conv_lhs => rw [h]
    simp
  rw [h1]
  exact h

theorem isMulRightInvariant_of_compactSpace (μ : Measure K) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  rw [eq_smul_haarProb μ]; infer_instance

theorem isInvInvariant_of_compactSpace (μ : Measure K) [μ.IsHaarMeasure] :
    μ.IsInvInvariant := by
  refine ⟨?_⟩
  rw [eq_smul_haarProb μ, Measure.inv, Measure.map_smul, map_inv_eq_self]

end Haar

theorem isCompact_unitaryGroup (n 𝕜 : Type*) [Fintype n] [DecidableEq n] [RCLike 𝕜] :
    IsCompact (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have hK : IsCompact (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
      Metric.closedBall (0 : 𝕜) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (s := (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
      Metric.closedBall (0 : 𝕜) 1 : Set (Matrix n n 𝕜))) hK
    (isClosed_unitary (R := Matrix n n 𝕜)) ?_
  intro U hU i _ j _
  simpa using entry_norm_bound_of_unitary hU i j

instance compactSpace_unitaryGroup (n 𝕜 : Type*) [Fintype n] [DecidableEq n] [RCLike 𝕜] :
    CompactSpace (Matrix.unitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup n 𝕜)

section Schur

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [Group K] [IsTopologicalGroup K] in

theorem integrable_of_continuous_of_compactSpace [IsFiniteMeasure μ] {E : Type*}
    [NormedAddCommGroup E] {f : K → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem inner_map_map_of_norm_map {G : Type*} [Monoid G] {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (ρ : Representation 𝕜 G E)
    (h : ∀ k v, ‖ρ k v‖ = ‖v‖) (k : G) (u v : E) : ⟪ρ k u, ρ k v⟫_𝕜 = ⟪u, v⟫_𝕜 :=
  LinearIsometry.inner_map_map ⟨ρ k, h k⟩ u v

variable [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)

noncomputable def rankOneAverage (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) (hσc : ∀ w, Continuous fun k => σ k w) (v : V) (w : W) :
    ρ.IntertwiningMap σ where
  toFun x := ∫ k, ⟪ρ k v, x⟫_ℂ • σ k w ∂μ
  map_add' x y := by
    have hi : ∀ z : V, Integrable (fun k => ⟪ρ k v, z⟫_ℂ • σ k w) μ := fun z =>
      integrable_of_continuous_of_compactSpace μ (((hρc v).inner continuous_const).smul (hσc w))
    rw [← integral_add (hi x) (hi y)]
    simp [add_smul]
  map_smul' c x := by
    simp [mul_smul, integral_smul]
  isIntertwining' g := by
    ext x
    have := FiniteDimensional.complete ℂ W
    have h1 := integral_mul_left_eq_self (μ := μ) (fun k => ⟪ρ k v, ρ g x⟫_ℂ • σ k w) g
    have h2 := (LinearMap.toContinuousLinearMap (σ g)).integral_comp_comm
      (integrable_of_continuous_of_compactSpace μ
        (((hρc v).inner (𝕜 := ℂ) (continuous_const (y := x))).smul (hσc w)))
    simp only [map_mul, Module.End.mul_apply, inner_map_map_of_norm_map ρ hρu] at h1
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← h1]
    simpa using h2

omit [FiniteDimensional ℂ V] in

theorem inner_rankOneAverage (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) (hσc : ∀ w, Continuous fun k => σ k w) (u v : V) (u' w : W) :
    ⟪u', rankOneAverage μ ρ σ hρc hρu hσc v w u⟫_ℂ =
      ∫ k, conj ⟪u, ρ k v⟫_ℂ * ⟪u', σ k w⟫_ℂ ∂μ := by
  have := FiniteDimensional.complete ℂ W
  have h := integral_inner (𝕜 := ℂ) (integrable_of_continuous_of_compactSpace μ
        (((hρc v).inner (𝕜 := ℂ) (continuous_const (y := u))).smul (hσc w))) u'
  refine Eq.trans h.symm ?_
  simp [inner_smul_right]

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K]
  [BorelSpace K] in

theorem finrank_pos_of_isIrreducible [h : ρ.IsIrreducible] : 0 < Module.finrank ℂ V := by
  rw [Module.finrank_pos_iff]
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : (⊥ : Subrepresentation ρ) = ⊤ :=
    Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact bot_ne_top this

end Schur

section Schur

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)

theorem integral_conj_inner_mul_inner [ρ.IsIrreducible] (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) (u v u' v' : V) :
    ∫ k, conj ⟪u, ρ k v⟫_ℂ * ⟪u', ρ k v'⟫_ℂ ∂μ =
      ⟪u', u⟫_ℂ * ⟪v, v'⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).2 (rankOneAverage μ ρ ρ hρc hρu hρc v v')
  have hA : ∀ x, rankOneAverage μ ρ ρ hρc hρu hρc v v' x = c • x := by
    intro x
    rw [← hc, Algebra.algebraMap_eq_smul_one]
    rfl
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_isIrreducible ρ).ne'
  set b := stdOrthonormalBasis ℂ V
  have htr : (Module.finrank ℂ V : ℂ) * c = ⟪v, v'⟫_ℂ := by
    have h1 : ∑ i, ⟪b i, rankOneAverage μ ρ ρ hρc hρu hρc v v' (b i)⟫_ℂ
        = (Module.finrank ℂ V : ℂ) * c := by
      simp [hA]
    rw [← h1]
    simp only [inner_rankOneAverage]
    have hi : ∀ i, Integrable (fun k => conj ⟪b i, ρ k v⟫_ℂ * ⟪b i, ρ k v'⟫_ℂ) μ :=
      fun i => integrable_of_continuous_of_compactSpace μ
        ((Complex.continuous_conj.comp (continuous_const.inner (hρc v))).mul
          (continuous_const.inner (hρc v')))
    rw [← integral_finsetSum _ (fun i _ => hi i)]
    simp [b.sum_inner_mul_inner, inner_map_map_of_norm_map ρ hρu]
  rw [← inner_rankOneAverage μ ρ ρ hρc hρu hρc, hA, inner_smul_right, ← htr]
  field_simp

theorem integral_conj_entry_mul_entry [ρ.IsIrreducible] (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ V) (i j i' j' : ι) :
    ∫ k, conj ⟪b i, ρ k (b j)⟫_ℂ * ⟪b i', ρ k (b j')⟫_ℂ ∂μ =
      if i = i' ∧ j = j' then (Module.finrank ℂ V : ℂ)⁻¹ else 0 := by
  rw [integral_conj_inner_mul_inner μ ρ hρc hρu, orthonormal_iff_ite.mp b.orthonormal,
    orthonormal_iff_ite.mp b.orthonormal]
  by_cases h1 : i = i' <;> by_cases h2 : j = j' <;> simp [h1, h2, eq_comm]

theorem integral_conj_character_mul_character_self [ρ.IsIrreducible]
    (hρc : ∀ v, Continuous fun k => ρ k v) (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) :
    ∫ k, conj (ρ.character k) * ρ.character k ∂μ = 1 := by
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_isIrreducible ρ).ne'
  set b := stdOrthonormalBasis ℂ V
  have hi : ∀ i j, Integrable (fun k => conj ⟪b i, ρ k (b i)⟫_ℂ * ⟪b j, ρ k (b j)⟫_ℂ) μ :=
    fun i j => integrable_of_continuous_of_compactSpace μ
      ((Complex.continuous_conj.comp (continuous_const.inner (hρc _))).mul
        (continuous_const.inner (hρc _)))
  simp only [Representation.character, LinearMap.trace_eq_sum_inner _ b, _root_.map_sum,
    Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  simp only [integral_finsetSum _ (fun j _ => hi _ j),
    integral_conj_entry_mul_entry μ ρ hρc hρu b]
  simp [hd]

end Schur

section Reducible

variable {𝕜 : Type*} [RCLike 𝕜]

def orthogonalSubrepresentation {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] {ρ : Representation 𝕜 G V} (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖)
    (U : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := U.toSubmoduleᗮ
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    have h := hv _ (U.apply_mem_toSubmodule g⁻¹ hu)
    rw [← inner_map_map_of_norm_map ρ hρu g] at h
    simpa using h

theorem isSemisimpleRepresentation_of_norm_map {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 G V)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) : ρ.IsSemisimpleRepresentation := by
  refine ⟨fun U => ⟨orthogonalSubrepresentation hρu U, ?_⟩⟩
  have h := U.toSubmodule.isCompl_orthogonal
  constructor
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.sup_eq_top

theorem isSemisimpleRepresentation_of_invariant_core {G V : Type*} [Group G] [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 G V)
    (c : InnerProductSpace.Core 𝕜 V) (hc : ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v) :
    ρ.IsSemisimpleRepresentation := by
  let _ : NormedAddCommGroup V := c.toNormedAddCommGroup
  let _ : InnerProductSpace 𝕜 V := InnerProductSpace.ofCore c.toCore
  refine isSemisimpleRepresentation_of_norm_map ρ fun k v => ?_
  rw [@norm_eq_sqrt_re_inner 𝕜, @norm_eq_sqrt_re_inner 𝕜]
  exact congrArg (fun z : 𝕜 => √(RCLike.re z)) (hc k v v)

theorem isIrreducible_toRepresentation_of_isAtom {F G V : Type*} [Field F] [Monoid G]
    [AddCommGroup V] [Module F V] {ρ : Representation F G V} {U : Subrepresentation ρ}
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  have hne : U.toSubmodule ≠ ⊥ := fun h => hU.1 (Subrepresentation.toSubmodule_injective h)
  have hnt : Nontrivial (Subrepresentation U.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h' : (⊥ : Submodule F U.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← U.toSubmodule.map_subtype_top, ← h', Submodule.map_bot]
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation ρ := ⟨S.toSubmodule.map U.toSubmodule.subtype, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, S.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hT : T ≤ U := U.toSubmodule.map_subtype_le S.toSubmodule
  have hinj := Submodule.map_injective_of_injective U.toSubmodule.injective_subtype
  rcases hU.le_iff.mp hT with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans (Submodule.map_bot _).symm
  · right
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans U.toSubmodule.map_subtype_top.symm

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

@[reducible] noncomputable def averageCore [MeasurableSpace K] [BorelSpace K] {V E : Type*}
    [AddCommGroup V] [Module 𝕜 V] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (ρ : Representation 𝕜 K V) (e : V →ₗ[𝕜] E) (he : Function.Injective e)
    (hc : ∀ v, Continuous fun k => e (ρ k v)) : InnerProductSpace.Core 𝕜 V where
  inner u v := ∫ k, ⟪e (ρ k u), e (ρ k v)⟫_𝕜 ∂haarProb K
  conj_inner_symm u v := by
    simp only [← integral_conj, inner_conj_symm]
  re_inner_nonneg v := by
    simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, integral_ofReal, RCLike.ofReal_re]
    exact integral_nonneg fun k => by positivity
  add_left u u' v := by
    have hi : ∀ z : V, Integrable (fun k => ⟪e (ρ k z), e (ρ k v)⟫_𝕜) (haarProb K) := fun z =>
      integrable_of_continuous_of_compactSpace _ ((hc z).inner (hc v))
    simp only [map_add, inner_add_left]
    exact integral_add (hi u) (hi u')
  smul_left u v r := by
    simp only [map_smul, inner_smul_left, integral_const_mul]
  definite v hv := by
    by_contra h
    simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, integral_ofReal,
      RCLike.ofReal_eq_zero] at hv
    refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := haarProb K) (x := 1)
      (f := fun k => ‖e (ρ k v)‖ ^ 2) ((hc v).norm.pow 2) (HasCompactSupport.of_compactSpace _)
      (fun k => by positivity) ?_).ne' hv
    simpa [map_eq_zero_iff e he] using h

theorem averageCore_inner_map_map [MeasurableSpace K] [BorelSpace K] {V E : Type*}
    [AddCommGroup V] [Module 𝕜 V] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (ρ : Representation 𝕜 K V) (e : V →ₗ[𝕜] E) (he : Function.Injective e)
    (hc : ∀ v, Continuous fun k => e (ρ k v)) (g : K) (u v : V) :
    (averageCore ρ e he hc).inner (ρ g u) (ρ g v) = (averageCore ρ e he hc).inner u v := by
  have h := integral_mul_right_eq_self (μ := haarProb K) (fun k => ⟪e (ρ k u), e (ρ k v)⟫_𝕜) g
  simp only [map_mul, Module.End.mul_apply] at h
  exact h

theorem exists_invariant_core_of_continuous_coeff {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 K V)
    (hρc : ∀ (l : Module.Dual 𝕜 V) (v : V), Continuous fun k => l (ρ k v)) :
    ∃ c : InnerProductSpace.Core 𝕜 V, ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v := by
  borelize K
  let b := Module.finBasis 𝕜 V
  let e : V ≃ₗ[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 V)) :=
    b.equivFun.trans (WithLp.linearEquiv 2 𝕜 _).symm
  have hc : ∀ v, Continuous fun k => e.toLinearMap (ρ k v) := fun v =>
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => hρc (b.coord i) v)
  exact ⟨averageCore ρ e.toLinearMap e.injective hc, averageCore_inner_map_map ρ _ _ hc⟩

theorem isSemisimpleRepresentation_of_continuous_coeff {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 K V)
    (hρc : ∀ (l : Module.Dual 𝕜 V) (v : V), Continuous fun k => l (ρ k v)) :
    ρ.IsSemisimpleRepresentation := by
  obtain ⟨c, hc⟩ := exists_invariant_core_of_continuous_coeff ρ hρc
  exact isSemisimpleRepresentation_of_invariant_core ρ c hc

variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]

theorem exists_invariant_core (ρ : Representation 𝕜 K V) (hρc : ∀ v, Continuous fun k => ρ k v) :
    ∃ c : InnerProductSpace.Core 𝕜 V, ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v :=
  exists_invariant_core_of_continuous_coeff ρ fun l v =>
    (LinearMap.continuous_of_finiteDimensional l).comp (hρc v)

end Reducible

end GlobalTheory
