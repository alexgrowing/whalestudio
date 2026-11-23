import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.roots_norm_le {l : ℕ} [Fact l.Prime] {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) (Qbar l)) (hZ : IntM Z) (a : Qbar l) (ha : Z.charpoly.IsRoot a) :
    ‖a‖ ≤ 1 := by
  classical
  have hdet : (Matrix.scalar (Fin n) a - Z).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact ha
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hc
    apply hv0
    funext j
    exact absurd ⟨j, Finset.mem_univ j⟩ hc
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) hne
  have hvi : v i ≠ 0 := by
    intro h0
    apply hv0
    funext j
    have hj := hi j (Finset.mem_univ j)
    rw [h0, norm_zero] at hj
    exact norm_le_zero_iff.1 hj
  have heq : a * v i = ∑ j, Z i j * v j := by
    have hvi' := congrFun hv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.zero_apply,
      sub_eq_zero] at hvi'
    rw [hvi']
    rfl
  have hle : ‖a‖ * ‖v i‖ ≤ 1 * ‖v i‖ := by
    rw [← norm_mul, heq, one_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j _
    rw [norm_mul]
    exact (mul_le_mul (hZ i j) (hi j (Finset.mem_univ j)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hvi)

theorem UpperTheory.V.Th.Nm.roots :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (Z : Matrix (Fin n) (Fin n) (Qbar l)), IntM Z → Z.charpoly.Separable → ∃ al : Fin n → Qbar l, Function.Injective al ∧ (∀ i, ‖al i‖ ≤ 1) ∧ Z.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) := by
  intro l _ n Z hZ hsep
  classical
  set p := Z.charpoly with hp
  set s := p.roots.toFinset with hs
  have hnd : p.roots.Nodup := Polynomial.nodup_roots hsep
  have hval : s.val = p.roots := by
    rw [hs, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
  have hcard : s.card = n := by
    rw [← Finset.card_val, hval, IsAlgClosed.card_roots_eq_natDegree, hp, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  let e : Fin n ≃ s := (finCongr hcard.symm).trans s.equivFin.symm
  refine ⟨fun i => (e i : Qbar l), ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    have hmem : (e i : Qbar l) ∈ p.roots := by
      rw [← hval]
      exact (e i).2
    exact roots_norm_le Z hZ _ (Polynomial.isRoot_of_mem_roots hmem)
  · rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic (Matrix.charpoly_monic Z), ← hval,
      ← Finset.prod_eq_multiset_prod, ← Finset.prod_coe_sort s]
    exact (Equiv.prod_comp e (fun x : s => Polynomial.X - Polynomial.C (x : Qbar l))).symm
