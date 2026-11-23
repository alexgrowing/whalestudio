import Mathlib

open scoped MonoidAlgebra

private theorem ss_proj {R V : Type} [Ring R] [AddCommGroup V] [Module R V]
    [IsSemisimpleModule R V] (s : Finset V) :
    ∃ (κ : Type) (_ : Fintype κ) (S : κ → Submodule R V) (P : κ → V →ₗ[R] V),
      (∀ i, IsAtom (S i)) ∧ (∀ i w, P i w ∈ S i) ∧ ∀ w ∈ s, ∑ i, P i w = w := by
  classical
  obtain ⟨t, e, -, ht⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R V
  let K : Finset t := s.biUnion fun w => (e w).support
  let Q : t → V →ₗ[R] V := fun m =>
    e.symm.toLinearMap ∘ₗ DFinsupp.lsingle (R := R) (M := fun m : t => m.1) m ∘ₗ
      DFinsupp.lapply (R := R) (M := fun m : t => m.1) m ∘ₗ e.toLinearMap
  let j : (m : t) → (m.1 →ₗ[R] V) := fun m =>
    e.symm.toLinearMap ∘ₗ DFinsupp.lsingle (R := R) (M := fun m : t => m.1) m
  have hj : ∀ m, Function.Injective (j m) := fun m =>
    e.symm.injective.comp (DFinsupp.single_injective (β := fun m : t => m.1) (i := m))
  refine ⟨K, inferInstance, fun i => LinearMap.range (j i.1), fun i => Q i.1, ?_, ?_, ?_⟩
  · intro i
    rw [← isSimpleModule_iff_isAtom]
    haveI := ht i.1
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hj i.1)).symm
  · intro i w
    exact ⟨e w i.1, rfl⟩
  · intro w hw
    rw [Finset.sum_coe_sort K (fun i => Q i w)]
    apply e.injective
    rw [map_sum]
    have h1 : ∀ i, e (Q i w) = DFinsupp.single i (e w i) := fun i => by simp [Q]
    simp_rw [h1]
    ext1 m
    rw [DFinsupp.finset_sum_apply]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      exact DFinsupp.single_eq_of_ne hb.symm
    · intro hm
      have : e w m = 0 := by
        by_contra h
        exact hm (Finset.mem_biUnion.mpr ⟨w, hw, DFinsupp.mem_support_iff.mpr h⟩)
      simp [this]

section
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W)

private noncomputable def toSub (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    Submodule ℂ[H] ρ.asModule where
  carrier := {x | ρ.asModuleEquiv x ∈ U}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact U.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq] at *
    rw [Representation.asModuleEquiv_map_smul]
    exact ρ.asAlgebraHom_mem_of_forall_mem U hU _ hx c

private theorem mem_toSub (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (x : ρ.asModule) :
    x ∈ toSub ρ U hU ↔ ρ.asModuleEquiv x ∈ U := Iff.rfl

private noncomputable def fromSub (N : Submodule ℂ[H] ρ.asModule) : Submodule ℂ W :=
  (N.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap

private theorem mem_fromSub (N : Submodule ℂ[H] ρ.asModule) (x : W) :
    x ∈ fromSub ρ N ↔ ρ.asModuleEquiv.symm x ∈ N := Iff.rfl

private theorem fromSub_inv (N : Submodule ℂ[H] ρ.asModule) (g : H) (u : W)
    (hu : u ∈ fromSub ρ N) : ρ g u ∈ fromSub ρ N := by
  rw [mem_fromSub] at *
  rw [Representation.asModuleEquiv_symm_map_rho]
  exact N.smul_mem _ hu

private theorem from_to (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    fromSub ρ (toSub ρ U hU) = U := by
  ext x; simp [mem_fromSub, mem_toSub]

private theorem from_le_iff (A B : Submodule ℂ[H] ρ.asModule) :
    fromSub ρ A ≤ fromSub ρ B ↔ A ≤ B := by
  constructor
  · intro h x hx
    have := @h (ρ.asModuleEquiv x) (by simpa [mem_fromSub] using hx)
    simpa [mem_fromSub] using this
  · intro h x hx
    exact h hx

private theorem from_inj {A B : Submodule ℂ[H] ρ.asModule} (h : fromSub ρ A = fromSub ρ B) :
    A = B :=
  le_antisymm ((from_le_iff ρ A B).mp h.le) ((from_le_iff ρ B A).mp h.ge)

private theorem from_bot : fromSub ρ ⊥ = ⊥ := by
  ext x; simp [mem_fromSub]

private theorem atom_iff (A : Submodule ℂ[H] ρ.asModule) :
    IsAtom A ↔ fromSub ρ A ≠ ⊥ ∧
      ∀ N ≤ fromSub ρ A, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = fromSub ρ A := by
  constructor
  · intro hA
    refine ⟨fun h => hA.1 (from_inj ρ (h.trans (from_bot ρ).symm)), fun N hN hi => ?_⟩
    rw [← from_to ρ N hi] at hN ⊢
    rcases hA.le_iff.mp ((from_le_iff ρ _ _).mp hN) with h | h
    · left; rw [h, from_bot]
    · right; rw [h]
  · rintro ⟨h0, h⟩
    refine ⟨fun hA => h0 (by rw [hA, from_bot]), fun B hB => ?_⟩
    rcases h _ ((from_le_iff ρ _ _).mpr hB.le) (fromSub_inv ρ B) with h | h
    · exact from_inj ρ (h.trans (from_bot ρ).symm)
    · exact absurd (from_inj ρ h) hB.ne

end

theorem UpperTheory.exists_equivariant_projections_of_sum_irreducible :
    ∀ (H W : Type) [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W), (∀ x : W, x ∈ ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) → ∀ M : Submodule ℂ W, FiniteDimensional ℂ M → ∃ (κ : Type) (_ : Fintype κ) (U : κ → Submodule ℂ W) (P : κ → W →ₗ[ℂ] W), (∀ i, U i ≠ ⊥ ∧ (∀ g, ∀ u ∈ U i, ρ g u ∈ U i) ∧ ∀ N ≤ U i, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U i) ∧ (∀ i w, P i w ∈ U i) ∧ (∀ i g w, P i (ρ g w) = ρ g (P i w)) ∧ ∀ w ∈ M, ∑ i, P i w = w := by
  intro H W _ _ _ ρ hsum M hM
  classical
  haveI : IsSemisimpleModule ℂ[H] ρ.asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    rw [eq_top_iff]
    intro y _
    have hle : (⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
        ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) ≤
        fromSub ρ (sSup {m : Submodule ℂ[H] ρ.asModule | IsSimpleModule ℂ[H] m}) := by
      refine iSup_le ?_
      rintro ⟨U, h0, hi, hU⟩
      show U ≤ _
      rw [← from_to ρ U hi, from_le_iff]
      apply le_sSup
      show IsSimpleModule ℂ[H] (toSub ρ U hi)
      rw [isSimpleModule_iff_isAtom, atom_iff, from_to]
      exact ⟨h0, hU⟩
    have := hle (hsum (ρ.asModuleEquiv y))
    simpa [mem_fromSub] using this
  obtain ⟨s, hs⟩ : M.FG := (Submodule.fg_iff_finiteDimensional M).mpr hM
  obtain ⟨κ, hκ, S, P, hS, hP, hsum'⟩ :=
    ss_proj (R := ℂ[H]) (V := ρ.asModule) (s.image ρ.asModuleEquiv.symm)
  let Q : κ → W →ₗ[ℂ] W := fun i =>
    ρ.asModuleEquiv.toLinearMap ∘ₗ (P i).restrictScalars ℂ ∘ₗ ρ.asModuleEquiv.symm.toLinearMap
  have hQ : ∀ i w, Q i w = ρ.asModuleEquiv (P i (ρ.asModuleEquiv.symm w)) := fun _ _ => rfl
  refine ⟨κ, hκ, fun i => fromSub ρ (S i), Q, ?_, ?_, ?_, ?_⟩
  · intro i
    have := (atom_iff ρ (S i)).mp (hS i)
    exact ⟨this.1, fromSub_inv ρ _, this.2⟩
  · intro i w
    rw [mem_fromSub, hQ, LinearEquiv.symm_apply_apply]
    exact hP i _
  · intro i g w
    apply ρ.asModuleEquiv.symm.injective
    rw [Representation.asModuleEquiv_symm_map_rho, hQ, hQ, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Representation.asModuleEquiv_symm_map_rho, map_smul]
  · intro w hw
    rw [← hs] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      simp_rw [hQ]
      rw [← map_sum, hsum' _ (Finset.mem_image_of_mem _ hx), LinearEquiv.apply_symm_apply]
    | zero => simp
    | add x y _ _ hx hy => simp_rw [map_add]; rw [Finset.sum_add_distrib, hx, hy]
    | smul c x _ hx => simp_rw [map_smul]; rw [← Finset.smul_sum, hx]
