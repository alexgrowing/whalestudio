import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.TendstoUniformlyOnDoublingLogOfContraction

open Filter Topology Set

namespace GlobalTheory

section Germ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eventually_eq_zero_of_tendsto_of_mem_discrete {α F : Type*} [AddCommGroup F]
    [TopologicalSpace F] {Γ : AddSubgroup F} (hΓ : IsDiscrete (Γ : Set F)) {l : Filter α}
    {f : α → F} (hf : Tendsto f l (𝓝 0)) (hm : ∀ᶠ a in l, f a ∈ Γ) : ∀ᶠ a in l, f a = 0 := by
  obtain ⟨U, hU, hU0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hΓ 0 Γ.zero_mem
  have h0 : (0 : F) ∈ U := (hU0.ge rfl).1
  filter_upwards [hf (hU.mem_nhds h0), hm] with a h1 h2
  exact hU0.le ⟨h1, h2⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem existsUnique_realLinear_of_eventually_add_mod_discrete {Γ : AddSubgroup F}
    (hΓ : IsDiscrete (Γ : Set F)) {g : E → F} (hc : ContinuousAt g 0) (h0 : g 0 = 0)
    (hg : ∀ᶠ p : E × E in 𝓝 0, g (p.1 + p.2) - g p.1 - g p.2 ∈ Γ) :
    ∃! L : E →L[ℝ] F, g =ᶠ[𝓝 0] L := by
  have ht : Tendsto g (𝓝 0) (𝓝 0) := by simpa [h0] using hc.tendsto
  have hadd : Tendsto (fun p : E × E ↦ p.1 + p.2) (𝓝 0) (𝓝 0) := by
    simpa using continuous_add.tendsto (0 : E × E)
  have h1 : Tendsto (fun p : E × E ↦ g (p.1 + p.2) - g p.1 - g p.2) (𝓝 0) (𝓝 0) := by
    simpa using ((ht.comp hadd).sub (ht.comp (continuous_fst.tendsto (0 : E × E)))).sub
      (ht.comp (continuous_snd.tendsto (0 : E × E)))
  obtain ⟨G, hG⟩ := exists_addMonoidHom_eventuallyEq (g := g) <| by
    filter_upwards [eventually_eq_zero_of_tendsto_of_mem_discrete hΓ h1 hg] with p hp
    rw [sub_sub, sub_eq_zero] at hp
    exact hp
  replace hG := hG.symm
  have hGc : Continuous G := continuous_of_continuousAt_zero G (hc.congr hG)
  refine ⟨G.toRealLinearMap hGc, hG, fun L hL ↦ ?_⟩
  have : (L : E →+ F) = G := addMonoidHom_eq_of_eventuallyEq (hL.symm.trans hG)
  ext x
  exact DFunLike.congr_fun this x

end Germ

section GermField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]

theorem realLinear_eq_fderiv_of_eventuallyEq {g : V → W} (hd : DifferentiableAt 𝕜 g 0)
    {L : V →L[ℝ] W} {c : W} (hL : ∀ᶠ z in 𝓝 0, g z = L z + c) :
    L = (fderiv 𝕜 g 0).restrictScalars ℝ :=
  ((L.hasFDerivAt.add_const c).congr_of_eventuallyEq hL).unique
    (hd.hasFDerivAt.restrictScalars ℝ)

theorem eventuallyEq_fderiv_of_eventually_add_mod_discrete {Γ : AddSubgroup W}
    (hΓ : IsDiscrete (Γ : Set W)) {g : V → W} (hd : DifferentiableAt 𝕜 g 0) (h0 : g 0 = 0)
    (hg : ∀ᶠ p : V × V in 𝓝 0, g (p.1 + p.2) - g p.1 - g p.2 ∈ Γ) :
    g =ᶠ[𝓝 0] fderiv 𝕜 g 0 := by
  obtain ⟨L, hL, -⟩ :=
    existsUnique_realLinear_of_eventually_add_mod_discrete hΓ hd.continuousAt h0 hg
  have := realLinear_eq_fderiv_of_eventuallyEq hd (L := L) (c := 0)
    (hL.mono fun z hz ↦ by rw [hz, add_zero])
  rw [this] at hL
  exact hL

end GermField

section Countable

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]

theorem subsingleton_of_countable_realModule (M : Type*) [AddCommGroup M] [Module ℝ M]
    [Countable M] : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 fun v ↦ by_contra fun hv ↦ ?_
  exact not_countable (α := ℝ) (smul_left_injective ℝ hv).countable

theorem realLinear_injective_of_countable_ker (L : M →ₗ[ℝ] N) (h : {x | L x = 0}.Countable) :
    Function.Injective L := by
  have : Countable (LinearMap.ker L) := h
  have := subsingleton_of_countable_realModule (LinearMap.ker L)
  exact LinearMap.ker_eq_bot.1 (Submodule.eq_bot_of_subsingleton)

theorem realLinear_surjective_of_mod_countable (L : M →ₗ[ℝ] N) {Γ : Set N} (hΓ : Γ.Countable)
    (h : ∀ y, ∃ x, y - L x ∈ Γ) : Function.Surjective L := by
  have : Countable Γ := hΓ
  have : Countable (N ⧸ LinearMap.range L) := by
    refine Function.Surjective.countable (f := fun γ : Γ ↦ (LinearMap.range L).mkQ γ) fun q ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨x, hx⟩ := h y
    exact ⟨⟨_, hx⟩, by simp [Submodule.Quotient.mk_eq_zero]⟩
  have := subsingleton_of_countable_realModule (N ⧸ LinearMap.range L)
  exact LinearMap.range_eq_top.1 (Submodule.Quotient.subsingleton_iff.1 this)

end Countable

section Lift

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {A : Type*} [AddCommGroup A]

theorem realLinear_eq_of_sub_mem_discrete {M : Type*} [AddCommGroup M] [Module ℝ M]
    {Γ : AddSubgroup F} (hΓ : IsDiscrete (Γ : Set F)) {L L' : M →ₗ[ℝ] F}
    (h : ∀ x, L x - L' x ∈ Γ) : L = L' := by
  ext x
  have ht : Tendsto (fun t : ℝ ↦ t • (L x - L' x)) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous fun t : ℝ ↦ t • (L x - L' x) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 := eventually_eq_zero_of_tendsto_of_mem_discrete hΓ ht
    (Eventually.of_forall fun t ↦ by simpa [smul_sub] using h (t • x))
  obtain ⟨t, ht0, ht⟩ := (h0.and self_mem_nhdsWithin).exists
  exact sub_eq_zero.1 ((smul_eq_zero.1 ht0).resolve_left ht)

theorem eventually_eq_lift_add {ex : E →+ A} {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) {g : E → F} (hc : ContinuousAt g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) {L : E →L[ℝ] F} (hL : ∀ z, ex' (L z) = ex z) :
    ∀ᶠ z in 𝓝 0, g z = L z + g 0 := by
  have h0 : ex' (g 0) = 0 := by simpa using hg.self_of_nhds
  have ht : Tendsto (fun z ↦ g z - (L z + g 0)) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto.sub ((L.continuous.tendsto 0).add_const (g 0))
  have := eventually_eq_zero_of_tendsto_of_mem_discrete hker ht <| by
    filter_upwards [hg] with z hz
    simp [AddMonoidHom.mem_ker, hz, hL, h0]
  filter_upwards [this] with z hz using sub_eq_zero.1 hz

theorem existsUnique_realLinear_lift_of_germ {ex : E →+ A} {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) {g : E → F} (hc : ContinuousAt g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : E →L[ℝ] F, ∀ z, ex' (L z) = ex z := by
  have h0 : ex' (g 0) = 0 := by simpa using hg.self_of_nhds
  have hadd : Tendsto (fun p : E × E ↦ p.1 + p.2) (𝓝 0) (𝓝 0) := by
    simpa using continuous_add.tendsto (0 : E × E)
  obtain ⟨L, hL, -⟩ := existsUnique_realLinear_of_eventually_add_mod_discrete hker
    (g := fun z ↦ g z - g 0) (hc.sub continuousAt_const) (sub_self _) <| by
      filter_upwards [hadd.eventually hg, (continuous_fst.tendsto (0 : E × E)).eventually hg,
        (continuous_snd.tendsto (0 : E × E)).eventually hg] with p h1 h2 h3
      simp [AddMonoidHom.mem_ker, h0, h1, h2, h3]
  have hL' : ex'.comp (L : E →+ F) = ex := addMonoidHom_eq_of_eventuallyEq <| by
    filter_upwards [hL, hg] with z h1 h2
    change ex' (L z) = ex z
    rw [← h1, map_sub, h0, h2, sub_zero]
  have hL'' : ∀ z, ex' (L z) = ex z := fun z ↦ DFunLike.congr_fun hL' z
  refine ⟨L, hL'', fun L' h' ↦ ContinuousLinearMap.coe_injective ?_⟩
  exact realLinear_eq_of_sub_mem_discrete hker fun x ↦ by
    simp [AddMonoidHom.mem_ker, h', hL'']

theorem exists_local_section_of_isDiscrete_ker {F : Type*} [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [TopologicalSpace A] {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) (hopen : 𝓝 (0 : A) ≤ map ex' (𝓝 0)) :
    ∃ s : A → F, s 0 = 0 ∧ ContinuousAt s 0 ∧ (∀ᶠ a in 𝓝 0, ex' (s a) = a) ∧
      ∀ᶠ z in 𝓝 0, s (ex' z) = z := by
  obtain ⟨U, hU, hU0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hker 0 ex'.ker.zero_mem
  obtain ⟨W, hW, hWU⟩ := exists_nhds_half_neg (hU.mem_nhds (hU0.ge rfl).1)
  have hinj : InjOn ex' W := fun x hx y hy hxy ↦
    sub_eq_zero.1 (hU0.le ⟨hWU x hx y hy, by simp [AddMonoidHom.mem_ker, hxy]⟩)
  have hs : ∀ᶠ z in 𝓝 0, Function.invFunOn ex' W (ex' z) = z := by
    filter_upwards [hW] with z hz using hinj.leftInvOn_invFunOn hz
  have h0 : Function.invFunOn ex' W 0 = 0 := by simpa using hs.self_of_nhds
  refine ⟨Function.invFunOn ex' W, h0, ?_, hopen ?_, hs⟩
  · rw [ContinuousAt, h0]
    exact (tendsto_map'_iff.2 (tendsto_id.congr' (hs.mono fun z hz ↦ hz.symm))).mono_left hopen
  · change ∀ᶠ a in map ex' (𝓝 0), _
    rw [eventually_map]
    filter_upwards [hs] with z hz
    rw [hz]

theorem existsUnique_realLinear_lift [TopologicalSpace A] {ex : E →+ A} {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) (hopen : 𝓝 (0 : A) ≤ map ex' (𝓝 0))
    (hc : ContinuousAt ex 0) : ∃! L : E →L[ℝ] F, ∀ z, ex' (L z) = ex z := by
  obtain ⟨s, -, hs, hs', -⟩ := exists_local_section_of_isDiscrete_ker hker hopen
  have ht : Tendsto ex (𝓝 0) (𝓝 0) := by simpa using hc.tendsto
  exact existsUnique_realLinear_lift_of_germ hker (g := s ∘ ex)
    (ContinuousAt.comp (by simpa using hs) hc) (ht.eventually hs')

end Lift

section LiftField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]
  {A : Type*} [AddCommGroup A]

theorem realLinear_lift_eq_fderiv {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {g : V → W} (hd : DifferentiableAt 𝕜 g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) {L : V →L[ℝ] W} (hL : ∀ z, ex' (L z) = ex z) :
    L = (fderiv 𝕜 g 0).restrictScalars ℝ :=
  realLinear_eq_fderiv_of_eventuallyEq hd (eventually_eq_lift_add hker hd.continuousAt hg hL)

theorem apply_fderiv_eq_of_germ {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {g : V → W} (hd : DifferentiableAt 𝕜 g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) (z : V) : ex' (fderiv 𝕜 g 0 z) = ex z := by
  obtain ⟨L, hL, -⟩ := existsUnique_realLinear_lift_of_germ hker hd.continuousAt hg
  have := hL z
  rwa [realLinear_lift_eq_fderiv hker hd hg hL] at this

theorem existsUnique_linear_lift_of_germ {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {g : V → W} (hd : DifferentiableAt 𝕜 g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : V →L[𝕜] W, ∀ z, ex' (L z) = ex z := by
  refine ⟨fderiv 𝕜 g 0, apply_fderiv_eq_of_germ hker hd hg, fun L hL ↦ ?_⟩
  have := realLinear_lift_eq_fderiv hker hd hg (L := L.restrictScalars ℝ) hL
  ext z
  exact DFunLike.congr_fun this z

theorem countable_of_isDiscrete_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} (hs : IsDiscrete s) : s.Countable := by
  have := hs.to_subtype
  exact countable_of_Lindelof_of_discrete (X := s)

theorem existsUnique_linearEquiv_lift_of_countable_ker
    [FiniteDimensional ℝ W] {ex : V →+ A} {ex' : W →+ A} (hc : (ex.ker : Set V).Countable)
    (hk' : IsDiscrete (ex'.ker : Set W)) (hr : ex'.range ≤ ex.range) {g : V → W}
    (hd : DifferentiableAt 𝕜 g 0) (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : V ≃L[𝕜] W, (∀ z, ex' (L z) = ex z) ∧ ex.ker.map (L : V →+ W) = ex'.ker := by
  obtain ⟨L, hL, hu⟩ := existsUnique_linear_lift_of_germ hk' hd hg
  have hc' := countable_of_isDiscrete_finiteDimensional hk'
  have hi : Function.Injective L :=
    realLinear_injective_of_countable_ker (L.restrictScalars ℝ).toLinearMap <|
      hc.mono fun x (hx : L x = 0) ↦ by simp [← hL x, hx]
  have hs : Function.Surjective L :=
    realLinear_surjective_of_mod_countable (L.restrictScalars ℝ).toLinearMap hc' fun y ↦ by
      obtain ⟨x, hx⟩ := hr ⟨y, rfl⟩
      exact ⟨x, by simp [hL, hx]⟩
  let e : V ≃ₗ[𝕜] W := LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩
  have he : Continuous e.symm :=
    (e.restrictScalars ℝ).symm.toLinearMap.continuous_of_finiteDimensional
  refine ⟨⟨e, L.continuous, he⟩, ⟨hL, ?_⟩, fun L' h' ↦ ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := hs y
    rw [AddMonoidHom.mem_ker, hL]
    exact AddSubgroup.mem_map_iff_mem (f := (L : V →+ W)) hi
  · have := hu (L' : V →L[𝕜] W) h'.1
    ext z
    exact DFunLike.congr_fun this z

theorem existsUnique_linearEquiv_of_uniformisations [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ W] {ex : V →+ A} {ex' : W →+ A} (hk : IsDiscrete (ex.ker : Set V))
    (hk' : IsDiscrete (ex'.ker : Set W)) (hr : ex'.range ≤ ex.range) {g : V → W}
    (hd : DifferentiableAt 𝕜 g 0) (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : V ≃L[𝕜] W, (∀ z, ex' (L z) = ex z) ∧ ex.ker.map (L : V →+ W) = ex'.ker :=
  existsUnique_linearEquiv_lift_of_countable_ker (countable_of_isDiscrete_finiteDimensional hk)
    hk' hr hd hg

end LiftField

section Kernel

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] {Λ : Submodule ℤ M} {Λ' : Submodule ℤ N}

def latticeQuotMap (Λ : Submodule ℤ M) (Λ' : Submodule ℤ N) (h : M →+ N)
    (hΛ : ∀ x ∈ Λ, h x ∈ Λ') : M ⧸ Λ →+ N ⧸ Λ' :=
  (Λ.mapQ Λ' h.toIntLinearMap hΛ).toAddMonoidHom

@[simp]
theorem latticeQuotMap_mk (h : M →+ N) (hΛ : ∀ x ∈ Λ, h x ∈ Λ') (x : M) :
    latticeQuotMap Λ Λ' h hΛ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x) := rfl

variable {φ : M ⧸ Λ →+ N ⧸ Λ'} {h : M →+ N}

theorem map_mem_of_quotient_lift
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) {x : M} (hx : x ∈ Λ) :
    h x ∈ Λ' := by
  rw [← Submodule.Quotient.mk_eq_zero, ← hφ, (Submodule.Quotient.mk_eq_zero Λ).2 hx, map_zero]

theorem mk_mem_ker_iff_of_quotient_lift
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) (x : M) :
    Submodule.Quotient.mk x ∈ φ.ker ↔ h x ∈ Λ' := by
  rw [AddMonoidHom.mem_ker, hφ, Submodule.Quotient.mk_eq_zero]

noncomputable def comapQuotEquivKer
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) :
    (Λ'.toAddSubgroup.comap h) ⧸ Λ.toAddSubgroup.addSubgroupOf (Λ'.toAddSubgroup.comap h) ≃+
      φ.ker :=
  QuotientAddGroup.liftEquiv _
    (φ := (Λ.mkQ.toAddMonoidHom.comp (Λ'.toAddSubgroup.comap h).subtype).codRestrict φ.ker
      fun x ↦ (mk_mem_ker_iff_of_quotient_lift hφ x).2 x.2)
    (by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Λ y
      exact ⟨⟨x, (mk_mem_ker_iff_of_quotient_lift hφ x).1 hy⟩, rfl⟩)
    (by
      ext x
      rw [AddMonoidHom.mem_ker, Subtype.ext_iff, AddSubgroup.mem_addSubgroupOf]
      exact (Submodule.Quotient.mk_eq_zero Λ).symm)

@[simp]
theorem comapQuotEquivKer_mk
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x))
    (x : Λ'.toAddSubgroup.comap h) :
    (comapQuotEquivKer hφ (QuotientAddGroup.mk x) : M ⧸ Λ) = Submodule.Quotient.mk (x : M) := rfl

def quotientLiftRestrict
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) : Λ →ₗ[ℤ] Λ' :=
  h.toIntLinearMap.restrict fun _ hx ↦ map_mem_of_quotient_lift hφ hx

@[simp]
theorem coe_quotientLiftRestrict
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) (x : Λ) :
    (quotientLiftRestrict hφ x : N) = h x := rfl

end Kernel

section Torsion

variable (K : Type*) [DivisionRing K] [CharZero K] {M : Type*} [AddCommGroup M] [Module K M]
  (Λ : Submodule ℤ M) (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem natCast_zsmul_eq_smul (x : M) : (n : ℤ) • x = (n : K) • x := by
  rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]

noncomputable def latticeToTorsion : Λ →ₗ[ℤ] Submodule.torsionBy ℤ (M ⧸ Λ) (n : ℤ) :=
  LinearMap.codRestrict _
    (Λ.mkQ ∘ₗ (DistribSMul.toAddMonoidHom M (n : K)⁻¹).toIntLinearMap ∘ₗ Λ.subtype) fun x ↦ by
      change (n : ℤ) • Λ.mkQ ((n : K)⁻¹ • (x : M)) = 0
      rw [← map_zsmul, natCast_zsmul_eq_smul K, smul_inv_smul₀ (NeZero.ne (n : K))]
      exact (Submodule.Quotient.mk_eq_zero Λ).2 x.2

noncomputable def modNEquivTorsion :
    ModN Λ n ≃ₗ[ℤ] Submodule.torsionBy ℤ (M ⧸ Λ) (n : ℤ) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [LinearMap.mem_ker, Subtype.ext_iff]
    change _ ↔ (Submodule.Quotient.mk ((n : K)⁻¹ • (x : M)) : M ⧸ Λ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      change (n : K)⁻¹ • (n : ℤ) • (y : M) ∈ Λ
      rw [natCast_zsmul_eq_smul K, inv_smul_smul₀ (NeZero.ne (n : K))]
      exact y.2
    · intro hx
      refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
      change (n : ℤ) • (n : K)⁻¹ • (x : M) = x
      rw [natCast_zsmul_eq_smul K, smul_inv_smul₀ (NeZero.ne (n : K))])).trans
    ((latticeToTorsion K Λ n).quotKerEquivOfSurjective (by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Λ y
      have hx : (n : ℤ) • x ∈ Λ := (Submodule.Quotient.mk_eq_zero Λ).1 hy
      refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
      change (Submodule.Quotient.mk ((n : K)⁻¹ • (n : ℤ) • x) : M ⧸ Λ) = Submodule.Quotient.mk x
      rw [natCast_zsmul_eq_smul K, inv_smul_smul₀ (NeZero.ne (n : K))]))

@[simp]
theorem coe_modNEquivTorsion_mk (x : Λ) :
    (modNEquivTorsion K Λ n (Submodule.Quotient.mk x) : M ⧸ Λ) =
      Submodule.Quotient.mk ((n : K)⁻¹ • (x : M)) := rfl

end Torsion

section RealTorus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem isDiscrete_ker_mkQ {M : Type*} [AddCommGroup M] [TopologicalSpace M] (Λ : Submodule ℤ M)
    [DiscreteTopology Λ] : IsDiscrete (Λ.mkQ.toAddMonoidHom.ker : Set M) := by
  have : (Λ.mkQ.toAddMonoidHom.ker : Set M) = Λ := by
    ext x
    exact Submodule.Quotient.mk_eq_zero Λ
  rw [this]
  exact DiscreteTopology.isDiscrete

end RealTorus

section Isogeny

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {Λ : Submodule ℤ E} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {Λ' : Submodule ℤ F} [DiscreteTopology Λ'] [IsZLattice ℝ Λ']
  {φ : E ⧸ Λ →+ F ⧸ Λ'} {h : E →ₗ[ℝ] F}

end Isogeny

section FieldTorus

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]

end FieldTorus

section ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℝ W]

end ComplexTorus

end GlobalTheory
