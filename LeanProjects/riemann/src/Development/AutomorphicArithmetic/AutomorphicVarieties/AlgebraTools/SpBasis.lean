import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SpStep

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private def UpperTheory.V.AlgebraTools.spIdx (n d : ℕ) (hd : d = n + 1) :
    (Fin d × ∀ i : Fin n, Fin (n - i)) ≃ (∀ i : Fin (n + 1), Fin (n + 1 - i)) where
  toFun p := fun i => Fin.cases (motive := fun i : Fin (n + 1) => Fin (n + 1 - i))
    ⟨p.1, by have := p.1.2; simp; omega⟩
    (fun j => ⟨p.2 j, by have := (p.2 j).2; simp only [Fin.val_succ]; omega⟩) i
  invFun c := (⟨c 0, by have := (c 0).2; simp at this; omega⟩,
    fun j => ⟨c j.succ, by have := (c j.succ).2; simp only [Fin.val_succ] at this; omega⟩)
  left_inv p := by
    ext <;> rfl
  right_inv c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem UpperTheory.V.AlgebraTools.spCard (n : ℕ) :
    Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fintype.card_congr (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), Fintype.card_prod,
      Fintype.card_fin, ih, Nat.factorial_succ]

theorem UpperTheory.V.AlgebraTools.splitAlg_basis :
    ∀ (n : ℕ) (R : Type) [CommRing R] (P : Polynomial R), P.Monic → P.natDegree = n →
      (∃ b : Module.Basis (∀ i : Fin n, Fin (n - i)) R (SplitAlg P n), ∀ c, b c = ∏ i, SplitAlg.root P n i ^ (c i : ℕ)) ∧
      Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  intro n
  induction n with
  | zero =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard 0⟩
    have hP : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    let f : SplitAlg P 0 →ₐ[R] R :=
      SplitAlg.lift P 0 (A := R) (fun i => i.elim0) (by simp [hP])
    have hfg : (Algebra.ofId R (SplitAlg P 0)).comp f = AlgHom.id R _ :=
      SplitAlg.hom_ext P 0 (fun i => i.elim0)
    have hgf : f.comp (Algebra.ofId R (SplitAlg P 0)) = AlgHom.id R R := Algebra.ext_id _ _ _
    let e : R ≃ₐ[R] SplitAlg P 0 := AlgEquiv.ofAlgHom (Algebra.ofId R _) f hfg hgf
    refine ⟨(Module.Basis.singleton (∀ i : Fin 0, Fin (0 - i)) R).map e.toLinearEquiv, fun c => ?_⟩
    simp [Module.Basis.singleton_apply]
  | succ n ih =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard (n + 1)⟩
    obtain ⟨inst1, inst2, h3, e, he⟩ := splitAlg_succ_equiv R n P hm hd
    have hroot : (Polynomial.map (algebraMap R (AdjoinRoot P)) P).IsRoot (AdjoinRoot.root P) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.isRoot_root P
    have hmul := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hQm : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).Monic := by
      refine Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C (AdjoinRoot.root P)) ?_
      rw [hmul]
      exact hm.map _
    have hQd : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).natDegree = n := by
      rcases subsingleton_or_nontrivial (AdjoinRoot P) with hs | hs
      · exfalso
        have hR : Nontrivial R := by
          rcases subsingleton_or_nontrivial R with hR | hR
          · rw [Subsingleton.elim P 0, Polynomial.natDegree_zero] at hd
            omega
          · exact hR
        have hne := (AdjoinRoot.powerBasis' hm).basis.ne_zero
          ⟨0, by rw [AdjoinRoot.powerBasis'_dim, hd]; omega⟩
        exact hne (Subsingleton.elim _ _)
      · rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
          hm.natDegree_map, hd, Polynomial.natDegree_X_sub_C]
        rfl
    obtain ⟨c, hc⟩ := (ih (AdjoinRoot P) _ hQm hQd).1
    let b := (AdjoinRoot.powerBasis' hm).basis.reindex
      (finCongr (by rw [AdjoinRoot.powerBasis'_dim, hd]))
    let c' := c.map e.symm.toLinearEquiv
    refine ⟨(b.smulTower c').reindex (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), fun k => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.smulTower_apply, Fin.prod_univ_succ]
    have hb : ∀ j, b j = AdjoinRoot.root P ^ (j : ℕ) := by
      intro j
      simp only [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
      rfl
    have hinv : ∀ i : Fin n, e.symm (SplitAlg.root _ n i) = SplitAlg.root P (n + 1) i.succ := by
      intro i
      rw [AlgEquiv.symm_apply_eq, he]
    simp only [c', Module.Basis.map_apply, hb, hc, Algebra.smul_def, map_pow, h3, map_prod,
      AlgEquiv.toLinearEquiv_apply, hinv]
    rfl
