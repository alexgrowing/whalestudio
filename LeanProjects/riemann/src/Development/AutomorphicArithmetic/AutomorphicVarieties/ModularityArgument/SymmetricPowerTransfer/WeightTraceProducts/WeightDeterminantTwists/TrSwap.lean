import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.MemHomogeneousExponentsOneBlock

open Polynomial UpperTheory.V.Z.Sym.Wt

open MvPolynomial in
private theorem homogeneous_trace_mul {d : ℕ} (n : ℕ) (g h : GL (Fin d) ℂ) :
    tr1 d n (g * h) = ∑ p ∈ deg1 d n ×ˢ deg1 d n, coeff p.1 (sbs (fun _ : Unit => g) (monomial p.2 1)) *
      coeff p.2 (sbs (fun _ : Unit => h) (monomial p.1 1)) := by
  classical
  have hcomp : ∀ P, sbs (fun _ : Unit => g * h) P = sbs (fun _ : Unit => g) (sbs (fun _ : Unit => h) P) := by
    intro P
    apply MvPolynomial.funext
    intro x
    rw [eval_sbs, eval_sbs, eval_sbs, ← act_mul]
    rfl
  rw [symPowTrace_eq_sum_coeff, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  have hmono : (monomial m (1 : ℂ)) ∈ MH d (fun _ : Unit => n) := by
    refine (memMH Unit d (fun _ => n) _).2 ?_
    intro m0 hm0 k
    rw [Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm0)]
    exact mem_homogeneousExponentsOneBlock.1 hm
  have hQ := sbs_mem (fun _ : Unit => h) hmono
  have hQsum : sbs (fun _ : Unit => h) (monomial m 1) =
      ∑ m' ∈ deg1 d n, monomial m' (coeff m' (sbs (fun _ : Unit => h) (monomial m 1))) := by
    conv_lhs => rw [(sbs (fun _ : Unit => h) (monomial m 1)).as_sum]
    apply Finset.sum_subset
    · intro m' hm'
      rw [mem_homogeneousExponentsOneBlock]
      exact (memMH Unit d (fun _ => n) _).1 hQ m' hm' ()
    · intro m' _ hm'
      rw [MvPolynomial.notMem_support_iff.1 hm', monomial_zero]
  rw [hcomp]
  conv_lhs => rw [hQsum]
  rw [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro m' _
  rw [show monomial m' (coeff m' (sbs (fun _ : Unit => h) (monomial m 1))) =
      coeff m' (sbs (fun _ : Unit => h) (monomial m 1)) • monomial m' (1 : ℂ) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm]

theorem UpperTheory.V.Z.Sym.Wt.trSwap :
    UpperTheory.V.Z.Sym.Wt.TrSwap := by
  classical
  intro I _ d n g
  have hinv : ∀ p, UpperTheory.V.Z.Sym.Wt.flip I d (UpperTheory.V.Z.Sym.Wt.flip I d p) = p := by
    intro p
    simp [UpperTheory.V.Z.Sym.Wt.flip]
  have hinj : Function.Injective (UpperTheory.V.Z.Sym.Wt.flip I d) := Function.LeftInverse.injective hinv
  have hglue : ∀ μ : I × Bool → Unit × Fin d →₀ ℕ,
      Finsupp.mapDomain (UpperTheory.V.Z.Sym.Wt.flip I d) (glue μ) = glue (fun k => μ (k.1, !k.2)) := by
    intro μ
    ext ⟨⟨i, b⟩, j⟩
    have := Finsupp.mapDomain_apply hinj (glue μ) ((i, !b), j)
    rw [show UpperTheory.V.Z.Sym.Wt.flip I d ((i, !b), j) = ((i, b), j) by
      simp [UpperTheory.V.Z.Sym.Wt.flip]] at this
    rw [this, glue_apply, glue_apply]
  rw [trace_blocks (K := I × Bool) (fun k => n k.1)
    ((sbs (dbl d g)).toLinearMap.comp (MvPolynomial.rename (UpperTheory.V.Z.Sym.Wt.flip I d)).toLinearMap)
    (biRep d n g * swp d n) (fun P => rfl)]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.rename_monomial, hglue,
    coeff_sbs_glue]
  simp_rw [homogeneous_trace_mul]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_nbij' (fun μ v => (μ (v, false), μ (v, true)))
    (fun x k => if k.2 then (x k.1).2 else (x k.1).1) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    rw [Fintype.mem_piFinset] at hμ ⊢
    intro v
    exact Finset.mem_product.2 ⟨hμ (v, false), hμ (v, true)⟩
  · intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    rintro ⟨v, b⟩
    cases b
    · exact (Finset.mem_product.1 (hx v)).1
    · exact (Finset.mem_product.1 (hx v)).2
  · intro μ _
    funext ⟨v, b⟩
    cases b <;> rfl
  · intro x _
    rfl
  · intro μ _
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro v _
    rw [Fintype.prod_bool]
    show MvPolynomial.coeff (μ (v, true))
        ((sbs fun _ : Unit => invT ℂ d (g v)) (MvPolynomial.monomial (μ (v, false)) 1)) *
      MvPolynomial.coeff (μ (v, false))
        ((sbs fun _ : Unit => g v) (MvPolynomial.monomial (μ (v, true)) 1)) = _
    exact mul_comm _ _
