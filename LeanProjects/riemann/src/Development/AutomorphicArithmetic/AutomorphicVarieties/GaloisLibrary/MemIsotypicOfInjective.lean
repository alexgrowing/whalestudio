import Mathlib

namespace UpperTheory.V.PiLin

theorem mem_isotypic_of_injective {R S Y V : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup Y] [Module R Y]
    [AddCommGroup V] [Module R V] [IsSimpleModule R S] (j : Y →ₗ[R] V) (hj : Function.Injective j)
    (h : ∀ y, j y ∈ isotypicComponent R V S) : isotypicComponent R Y S = ⊤ := by
  classical
  have hf : Function.Injective (j.codRestrict (isotypicComponent R V S) h) :=
    fun a b hab => hj (congrArg Subtype.val hab)
  have hiso : IsIsotypicOfType R Y S :=
    (IsIsotypicOfType.isotypicComponent R V S).of_injective _ hf
  have : IsSemisimpleModule R Y := IsSemisimpleModule.of_injective _ hf
  rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top]
  refine sSup_le fun m hm => ?_
  have : IsSimpleModule R m := hm
  exact le_sSup (hiso m)

theorem iso_sub {H S Y V : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H S) (π : Representation ℂ H Y) (ρ : Representation ℂ H V)
    (hσ : σ.IsIrreducible) (j : Y →ₗ[ℂ] V) (hj : Function.Injective j) (he : ∀ g y, j (π g y) = ρ g (j y))
    (h : ∀ y, j y ∈ ⨆ f : {f : S →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) (y : Y) :
    y ∈ ⨆ f : {f : S →ₗ[ℂ] Y // ∀ g v, f (σ g v) = π g (f v)}, LinearMap.range f.1 := by
  classical
  haveI : σ.IsIrreducible := hσ
  let J : Representation.IntertwiningMap π ρ := j.intertwiningMap_of_isIntertwiningMap π ρ he
  let j' := Representation.IntertwiningMap.equivLinearMapAsModule π ρ J
  have hj' : Function.Injective j' := hj
  have h' : ∀ z, j' z ∈ isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ.asModule := by
    intro z
    have hz := h z
    refine Submodule.iSup_induction _ (motive := fun x => ρ.asModuleEquiv.symm x ∈
      isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ.asModule) hz ?_ ?_ ?_
    · rintro f x ⟨v, rfl⟩
      let F := Representation.IntertwiningMap.equivLinearMapAsModule σ ρ
        (f.1.intertwiningMap_of_isIntertwiningMap σ ρ f.2)
      have hle : LinearMap.range F ≤ isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ.asModule := by
        rcases F.injective_or_eq_zero with hF | hF
        · exact le_sSup ⟨(LinearEquiv.ofInjective F hF).symm⟩
        · rw [hF, LinearMap.range_zero]
          exact bot_le
      exact hle ⟨σ.asModuleEquiv.symm v, rfl⟩
    · simp
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  have htop := mem_isotypic_of_injective j' hj' h'
  have hy : π.asModuleEquiv.symm y ∈ isotypicComponent (MonoidAlgebra ℂ H) π.asModule σ.asModule := by
    rw [htop]
    exact Submodule.mem_top
  rw [isotypicComponent, sSup_eq_iSup'] at hy
  have key := Submodule.iSup_induction _ (motive := fun x => π.asModuleEquiv x ∈
      ⨆ f : {f : S →ₗ[ℂ] Y // ∀ g v, f (σ g v) = π g (f v)}, LinearMap.range f.1) hy
    (by
      rintro ⟨m, ⟨e⟩⟩ x hx
      let L : σ.asModule →ₗ[MonoidAlgebra ℂ H] π.asModule := m.subtype ∘ₗ e.symm.toLinearMap
      let F := (Representation.IntertwiningMap.equivLinearMapAsModule σ π).symm L
      refine Submodule.mem_iSup_of_mem
        ⟨F.toLinearMap, fun g v => Representation.IntertwiningMap.isIntertwining σ π F g v⟩
        ⟨σ.asModuleEquiv (e ⟨x, hx⟩), ?_⟩
      show (L (e ⟨x, hx⟩) : π.asModule) = x
      simp [L])
    (by simp)
    (by
      intro x z hx hz
      rw [map_add]
      exact Submodule.add_mem _ hx hz)
  simpa using key

theorem exists_desc {M V : Type} [AddCommGroup V] [Module ℂ V] (s s' : M → V)
    (h : ∀ c : M →₀ ℂ, Finsupp.linearCombination ℂ s c = 0 → Finsupp.linearCombination ℂ s' c = 0) :
    ∃ T : V →ₗ[ℂ] V, ∀ m, T (s m) = s' m := by
  classical
  have hk : LinearMap.ker (Finsupp.linearCombination ℂ s) ≤ LinearMap.ker (Finsupp.linearCombination ℂ s') :=
    fun c hc => LinearMap.mem_ker.mpr (h c (LinearMap.mem_ker.mp hc))
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((LinearMap.ker (Finsupp.linearCombination ℂ s)).liftQ (Finsupp.linearCombination ℂ s') hk ∘ₗ
      (Finsupp.linearCombination ℂ s).quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, fun m => ?_⟩
  have hm : s m = Finsupp.linearCombination ℂ s (Finsupp.single m 1) := by simp
  have := LinearMap.congr_fun hg ⟨_, LinearMap.mem_range_self _ (Finsupp.single m (1 : ℂ))⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at this
  rw [hm, this]
  simp

private theorem exists_equivariant_projection_onto_invariant_submodule {R V ι : Type*} [AddCommGroup V] [Module ℂ V] (T : R → V →ₗ[ℂ] V)
    (χ : ι → R → ℂ) (a : R → ℂ) (s : Finset ι) (v : ι → V)
    (hv : ∀ i ∈ s, ∀ t, T t (v i) = χ i t • v i) (ha : ∀ i ∈ s, χ i ≠ a)
    (hx : ∀ t, T t (∑ i ∈ s, v i) = a t • ∑ i ∈ s, v i) : ∑ i ∈ s, v i = 0 := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | insert b s hb ih =>
    obtain ⟨t, ht⟩ := Function.ne_iff.mp (ha b (Finset.mem_insert_self b s))
    have hvs : ∀ i ∈ s, ∀ t, T t (v i) = χ i t • v i :=
      fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have key : (a t - χ b t) • ∑ i ∈ insert b s, v i = ∑ i ∈ s, (χ i t - χ b t) • v i := by
      rw [sub_smul, ← hx t, Finset.sum_insert hb, map_add, map_sum,
        Finset.sum_congr rfl (fun i hi => hvs i hi t), hv b (Finset.mem_insert_self b s) t]
      simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_add]
      abel
    have hz := ih (fun i => (χ i t - χ b t) • v i)
      (fun i hi t' => by rw [map_smul, hvs i hi t', smul_comm])
      (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun t' => by rw [← key, map_smul, hx t', smul_comm])
    rw [← key] at hz
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm ht))

theorem exists_proj {R G V : Type} {J : Type 1} [AddCommGroup V] [Module ℂ V] (T : R → V →ₗ[ℂ] V) (π : G → V →ₗ[ℂ] V)
    (E : Submodule ℂ V) (hE : ∀ g, ∀ F ∈ E, π g F ∈ E) (hc : ∀ t g, ∀ F ∈ E, T t (π g F) = π g (T t F))
    (W : J → Submodule ℂ V) (χ : J → R → ℂ) (hW : ∀ j t, ∀ F ∈ W j, T t F = χ j t • F) (hsup : E = ⨆ j, W j)
    (F0 : V) (h0 : F0 ∈ E) (hne : F0 ≠ 0) :
    ∃ (j0 : J) (Y : Submodule ℂ V) (p : V →ₗ[ℂ] Y), W j0 ≠ ⊥ ∧ (∀ g, ∀ F ∈ Y, π g F ∈ Y) ∧ p F0 ≠ 0 ∧
      (∀ t, ∀ F ∈ E, p (T t F) = χ j0 t • p F) ∧ (∀ g, ∀ F ∈ E, (p (π g F) : V) = π g (p F)) ∧
      Y ≤ ⨆ j : {j // χ j = χ j0}, W j := by
  classical
  have hYe : ∀ c, ∀ x ∈ ⨆ j : {j // χ j = c}, W j, ∀ t, T t x = c t • x := by
    intro c x hx t
    refine Submodule.iSup_induction _ (motive := fun x => T t x = c t • x) hx ?_ ?_ ?_
    · intro j y hy
      rw [hW j.1 t y hy, j.2]
    · simp
    · intro y z hy hz
      rw [map_add, hy, hz, smul_add]
  have hKz : ∀ c, ∀ x ∈ ⨆ j : {j // χ j ≠ c}, W j, (∀ t, T t x = c t • x) → x = 0 := by
    intro c x hx hxe
    obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
    obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hs
    subst hμ
    exact exists_equivariant_projection_onto_invariant_submodule T (fun j : {j // χ j ≠ c} => χ j.1) c s (fun j => (μ j : V))
      (fun j _ t => hW j.1 t _ (μ j).2) (fun j _ => j.2) hxe
  have hsplit : ∀ c, E = (⨆ j : {j // χ j = c}, W j) ⊔ ⨆ j : {j // χ j ≠ c}, W j := by
    intro c
    rw [hsup, iSup_split W (fun j => χ j = c), iSup_subtype', iSup_subtype']
  have hTK : ∀ c t, ∀ x ∈ ⨆ j : {j // χ j ≠ c}, W j, T t x ∈ ⨆ j : {j // χ j ≠ c}, W j := by
    intro c t x hx
    refine Submodule.iSup_induction _ (motive := fun x => T t x ∈ ⨆ j : {j // χ j ≠ c}, W j) hx
      ?_ ?_ ?_
    · intro j y hy
      rw [hW j.1 t y hy]
      exact Submodule.mem_iSup_of_mem j (Submodule.smul_mem _ _ hy)
    · simp
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  have hEY : ∀ c, ∀ F ∈ E, (∀ t, T t F = c t • F) → F ∈ ⨆ j : {j // χ j = c}, W j := by
    intro c F hF hFe
    rw [hsplit c] at hF
    obtain ⟨y, hy, k, hk, rfl⟩ := Submodule.mem_sup.mp hF
    have hke : ∀ t, T t k = c t • k := by
      intro t
      have h1 := hFe t
      rw [map_add, hYe c y hy t, smul_add] at h1
      exact add_left_cancel h1
    rw [hKz c k hk hke, add_zero]
    exact hy
  have hYE : ∀ c, (⨆ j : {j // χ j = c}, W j) ≤ E := by
    intro c
    rw [hsplit c]
    exact le_sup_left
  have hKE : ∀ c, (⨆ j : {j // χ j ≠ c}, W j) ≤ E := by
    intro c
    rw [hsplit c]
    exact le_sup_right
  have hπY : ∀ c g, ∀ F ∈ ⨆ j : {j // χ j = c}, W j, π g F ∈ ⨆ j : {j // χ j = c}, W j := by
    intro c g F hF
    refine hEY c _ (hE g F (hYE c hF)) fun t => ?_
    rw [hc t g F (hYE c hF), hYe c F hF t, map_smul]
  have hπK : ∀ c g, ∀ x ∈ ⨆ j : {j // χ j ≠ c}, W j, π g x ∈ ⨆ j : {j // χ j ≠ c}, W j := by
    intro c g x hx
    refine Submodule.iSup_induction _ (motive := fun x => π g x ∈ ⨆ j : {j // χ j ≠ c}, W j) hx
      ?_ ?_ ?_
    · intro j y hy
      have h1 : π g y ∈ ⨆ i : {i // χ i = χ j.1}, W i :=
        hπY (χ j.1) g y (Submodule.mem_iSup_of_mem (⟨j.1, rfl⟩ : {i // χ i = χ j.1}) hy)
      have hle : (⨆ i : {i // χ i = χ j.1}, W i) ≤ ⨆ j : {j // χ j ≠ c}, W j :=
        iSup_le fun i => le_iSup (fun j : {j // χ j ≠ c} => W j.1) ⟨i.1, by rw [i.2]; exact j.2⟩
      exact hle h1
    · simp
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  have h0' := h0
  rw [hsup] at h0'
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp h0'
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hs
  obtain ⟨j1, -, hu⟩ : ∃ j1 ∈ s, ∑ i ∈ s.filter (fun i => χ i = χ j1), (μ i : V) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [← hμ, ← Finset.sum_fiberwise_of_maps_to (g := χ) (t := s.image χ)
      (fun i hi => Finset.mem_image_of_mem χ hi)]
    refine Finset.sum_eq_zero fun c hc => ?_
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    exact hcon j hj
  obtain ⟨j0, hj0, hμ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  have hχ : χ j0 = χ j1 := (Finset.mem_filter.mp hj0).2
  rw [← hχ] at hu
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl E
  have hYK : IsCompl (⨆ j : {j // χ j = χ j0}, W j) ((⨆ j : {j // χ j ≠ χ j0}, W j) ⊔ C) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxY hxKC
      obtain ⟨k, hk, c', hc', rfl⟩ := Submodule.mem_sup.mp hxKC
      have hc'E : c' ∈ E := by
        have h2 : c' = (k + c') - k := by abel
        rw [h2]
        exact Submodule.sub_mem _ (hYE _ hxY) (hKE _ hk)
      have hc'0 : c' = 0 := (Submodule.disjoint_def.mp hC.disjoint) c' hc'E hc'
      subst hc'0
      rw [add_zero] at hxY ⊢
      exact hKz (χ j0) k hk (hYe (χ j0) k hxY)
    · rw [codisjoint_iff, ← sup_assoc, ← hsplit (χ j0)]
      exact hC.sup_eq_top
  have hpY : ∀ y (hy : y ∈ ⨆ j : {j // χ j = χ j0}, W j),
      Submodule.projectionOnto _ _ hYK y = ⟨y, hy⟩ :=
    fun y hy => Submodule.projectionOnto_apply_of_mem_left hYK hy
  have hpK : ∀ k ∈ ⨆ j : {j // χ j ≠ χ j0}, W j, Submodule.projectionOnto _ _ hYK k = 0 :=
    fun k hk => Submodule.projectionOnto_apply_of_mem_right hYK (Submodule.mem_sup_left hk)
  refine ⟨j0, _, Submodule.projectionOnto _ _ hYK, ?_, hπY (χ j0), ?_, ?_, ?_, le_rfl⟩
  · intro hbot
    exact hμ0 ((Submodule.eq_bot_iff _).mp hbot _ (μ j0).2)
  · have huY : (∑ i ∈ s.filter (fun i => χ i = χ j0), (μ i : V)) ∈ ⨆ j : {j // χ j = χ j0}, W j :=
      Submodule.sum_mem _ fun i hi =>
        Submodule.mem_iSup_of_mem (⟨i, (Finset.mem_filter.mp hi).2⟩ : {j // χ j = χ j0}) (μ i).2
    have hrK : (∑ i ∈ s.filter (fun i => ¬ χ i = χ j0), (μ i : V)) ∈ ⨆ j : {j // χ j ≠ χ j0}, W j :=
      Submodule.sum_mem _ fun i hi =>
        Submodule.mem_iSup_of_mem (⟨i, (Finset.mem_filter.mp hi).2⟩ : {j // χ j ≠ χ j0}) (μ i).2
    intro hp
    apply hu
    rw [← hμ, ← Finset.sum_filter_add_sum_filter_not s (fun i => χ i = χ j0), map_add,
      hpK _ hrK, add_zero, hpY _ huY] at hp
    simpa using congrArg Subtype.val hp
  · intro t F hF
    rw [hsplit (χ j0)] at hF
    obtain ⟨y, hy, k, hk, rfl⟩ := Submodule.mem_sup.mp hF
    simp only [map_add, map_smul, hYe _ y hy t, hpK _ hk, hpK _ (hTK _ t k hk), add_zero]
  · intro g F hF
    rw [hsplit (χ j0)] at hF
    obtain ⟨y, hy, k, hk, rfl⟩ := Submodule.mem_sup.mp hF
    simp [hpK _ hk, hpK _ (hπK _ g k hk), hpY _ hy, hpY _ (hπY _ g y hy)]

end UpperTheory.V.PiLin
