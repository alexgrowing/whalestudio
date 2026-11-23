import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.CoordSub

open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem exists_eigenbasis_of_separable_charpoly {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.charpoly.Separable) :
    ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K), Function.Injective l ∧
      ∀ i, A *ᵥ b i = l i • b i := by
  classical
  have hnd : A.charpoly.roots.Nodup := Polynomial.nodup_roots hA
  have hcard : A.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : A.charpoly.roots.toFinset ≃ Fin n := Finset.equivFinOfCardEq hcard
  let l : Fin n → K := fun i => (e.symm i : K)
  have hl : Function.Injective l := fun i j h => e.symm.injective (Subtype.ext h)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A) (l i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) l hl v hv
  have hsp : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Module.finrank_fintype_fun_eq_card])
  refine ⟨Module.Basis.mk hli hsp.ge, l, hl, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  have := (hv i).apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

theorem UpperTheory.V.Ws.invariant_submodule_eq_span_eigenbasis_of_separable :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K), M.charpoly.Separable →
      ∃ b : Module.Basis (Fin n) K (Fin n → K), ∀ W : Submodule K (Fin n → K), (∀ v ∈ W, M *ᵥ v ∈ W) →
        W = Submodule.span K (b '' {i | b i ∈ W}) := by
  classical
  intro K _ _ n M hM
  obtain ⟨b, l, hl, hb⟩ := exists_eigenbasis_of_separable_charpoly M hM
  refine ⟨b, fun W hW => le_antisymm ?_ ?_⟩
  · have hcomm : ∀ x : Fin n → K, b.equivFun.symm (diagonal l *ᵥ x) = M *ᵥ b.equivFun.symm x := by
      intro x
      rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hb, mulVec_diagonal, smul_smul, mul_comm]
    have key := UpperTheory.V.AlgebraTools.coordSub K (Fin n) l
      (fun i j h => (sub_ne_zero.mpr (fun h' => h (hl h'))).isUnit)
      (W.comap b.equivFun.symm.toLinearMap)
      (fun w hw => by
        rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hw ⊢
        rw [hcomm]
        exact hW _ hw)
    intro v hv
    have h1 : ∀ i, b.repr v i • b i ∈ W := by
      intro i
      have h2 := key (b.equivFun v) (by
        rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]; exact hv) i
      rw [Submodule.mem_comap, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
        Finset.sum_eq_single i (fun j _ h => by rw [Pi.single_eq_of_ne h, zero_smul])
          (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, Module.Basis.equivFun_apply] at h2
      exact h2
    rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h : b.repr v i = 0
    · rw [h, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, (W.smul_mem_iff h).mp (h1 i), rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hi
