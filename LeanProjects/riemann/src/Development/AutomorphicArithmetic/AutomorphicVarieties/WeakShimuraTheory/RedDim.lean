import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem redDim_set {k V X : Type} [Field k] [AddCommGroup V] [Module k V] (n : ℕ)
    (h : Module.rank k V ≤ n) (M : Set X) (ev : X → Module.Dual k V) :
    ∃ S : Finset X, (S : Set X) ⊆ M ∧ S.card ≤ n ∧ ∀ v, (∀ s ∈ S, ev s v = 0) → ∀ x ∈ M, ev x v = 0 := by
  classical
  haveI : Module.Finite k V := Module.rank_lt_aleph0_iff.1 (h.trans_lt (Cardinal.natCast_lt_aleph0))
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent k (ev '' M)
  have hfin : b.Finite := hli.set_finite_of_isNoetherian
  haveI := hfin.fintype
  have hcard : Fintype.card b ≤ n := by
    refine hli.fintype_card_le_finrank.trans ?_
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_le_of_rank_le h
  choose σ hσ hσ' using fun y : b => hb y.2
  refine ⟨Finset.univ.image σ, ?_, Finset.card_image_le.trans hcard, fun v hv x hx => ?_⟩
  · intro s hs
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hs
    exact hσ y
  · have h1 : ev x ∈ Submodule.span k b := hsp ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    have h2 : Submodule.span k b ≤ LinearMap.ker (Module.Dual.eval k V v) := by
      refine Submodule.span_le.2 fun y hy => ?_
      have := hv _ (Finset.mem_image_of_mem σ (Finset.mem_univ ⟨y, hy⟩))
      rw [hσ'] at this
      exact this
    exact h2 h1

private theorem redDim_dual (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.IsTorsionBySet O M (maximalIdeal O)) (x : M) (hx : x ≠ 0) :
    ∃ D : M →ₗ[O] ResidueField O, D x ≠ 0 := by
  letI : Module (ResidueField O) M := h.module
  haveI : IsScalarTower O (ResidueField O) M := h.isScalarTower
  have := (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).not.2 hx
  push Not at this
  obtain ⟨φ, hφ⟩ := this
  exact ⟨φ.restrictScalars O, hφ⟩

private theorem redDim_der {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (I : Ideal R) (hIm : I ≤ maximalIdeal R) (hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I)
    (h2 : maximalIdeal R * maximalIdeal R ≤ I) (x : R) (hx : x ∈ maximalIdeal R) (hxI : x ∉ I) :
    ∃ D ∈ PtDer (res O R) (ResidueField O), D x ≠ 0 ∧ ∀ y ∈ I, D y = 0 := by
  let N : Submodule O R := I.restrictScalars O ⊔ Submodule.span O {1}
  have hIN : ∀ y ∈ I, y ∈ N := fun y hy => Submodule.mem_sup_left hy
  have hON : ∀ a : O, algebraMap O R a ∈ N := fun a =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, (Algebra.algebraMap_eq_smul_one a).symm⟩)
  have hxN : N.mkQ x ≠ 0 := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Submodule.Quotient.mk_eq_zero N).1 h)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [← Algebra.algebraMap_eq_smul_one] at hyz
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hx (hIm hy)
      rwa [← hyz, add_sub_cancel_left] at this
    have h2 : a ∈ maximalIdeal O := fun h => h1 (h.map _)
    exact hxI (hyz ▸ I.add_mem hy (hO a h2))
  have htor : Module.IsTorsionBySet O (R ⧸ N) (maximalIdeal O) := by
    rintro y ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    show a • N.mkQ y = 0
    rw [← map_smul]
    refine (Submodule.Quotient.mk_eq_zero N).2 (hIN _ ?_)
    rw [Algebra.smul_def]
    exact I.mul_mem_right _ (hO a ha)
  obtain ⟨φ, hφ⟩ := redDim_dual O _ htor _ hxN
  let D : R →ₗ[O] ResidueField O := φ ∘ₗ N.mkQ
  have hD : ∀ y ∈ N, D y = 0 := fun y hy => by
    show φ (N.mkQ y) = 0
    rw [show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]
  have hres : ∀ (y : R) (a : O), y - algebraMap O R a ∈ maximalIdeal R → res O R y = algebraMap O _ a :=
    fun y a ha => by
      have := (res_eq_zero_iff O R _).2 ha
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  refine ⟨D, fun y z => ?_, hφ, fun y hy => hD y (hIN y hy)⟩
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
  obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) z
  have h1 : D ((y - algebraMap O R a) * (z - algebraMap O R b)) = 0 :=
    hD _ (hIN _ (h2 (Ideal.mul_mem_mul ha hb)))
  have h2 : y * z = (y - algebraMap O R a) * (z - algebraMap O R b) + a • z + b • y
      - algebraMap O R (a * b) := by
    simp only [Algebra.smul_def, map_mul]; ring
  rw [h2, map_sub, map_add, map_add, h1, hD _ (hON _), map_smul, map_smul, hres y a ha, hres z b hb]
  simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]; ring

theorem UpperTheory.V.Ws.redDim :
    ∀ {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (n : ℕ),
          Module.rank (ResidueField Λ) (PtDer (res Λ R) (ResidueField Λ)) ≤ n → ringKrullDim R ≤ (n + 1 : ℕ) := by
  intro Λ _ _ _ R _ _ _ n h
  classical
  let ev : R → Module.Dual (ResidueField Λ) (PtDer (res Λ R) (ResidueField Λ)) := fun x =>
    { toFun := fun D => D.1 x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  obtain ⟨S, hS, hcard, hv⟩ := redDim_set n h (maximalIdeal R) ev
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Λ
  let T : Finset R := insert (algebraMap Λ R ϖ) S
  have hT : Ideal.span (T : Set R) ≤ maximalIdeal R := by
    refine Ideal.span_le.2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact fun hu => hϖ.not_isUnit (IsLocalHom.map_nonunit ϖ hu)
    · exact hS hy
  have hle : maximalIdeal R ≤ Ideal.span (T : Set R) ⊔ maximalIdeal R * maximalIdeal R := by
    intro x hx
    by_contra hxI
    obtain ⟨D, hD, hDx, hDI⟩ := redDim_der (O := Λ) _ (sup_le hT Ideal.mul_le_right) (fun a ha => by
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.subset_span (Finset.mem_insert_self _ _))))
      le_sup_right x hx hxI
    exact hDx (hv ⟨D, hD⟩ (fun s hs =>
      hDI s (Ideal.mem_sup_left (Ideal.subset_span (Finset.mem_insert_of_mem hs)))) x hx)
  have heq : maximalIdeal R = Ideal.span (T : Set R) :=
    le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson _) hle) hT
  refine (ringKrullDim_le_spanFinrank_maximalIdeal R).trans ?_
  have h3 : (maximalIdeal R).spanFinrank ≤ n + 1 := by
    rw [heq]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite T.finite_toSet).trans ?_
    rw [Set.ncard_coe_finset]
    exact (Finset.card_insert_le _ _).trans (by omega)
  exact_mod_cast h3
