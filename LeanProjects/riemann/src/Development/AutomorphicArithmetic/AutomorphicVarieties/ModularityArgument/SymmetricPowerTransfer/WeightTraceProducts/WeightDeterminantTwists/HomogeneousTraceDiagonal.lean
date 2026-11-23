import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.MemHomogeneousExponentsOneBlock

open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem tri (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (f : Module.End ℂ V),
    Module.finrank ℂ V = d → ∃ b : Module.Basis (Fin d) ℂ V, ∀ i j, i < j → b.repr (f (b j)) i = 0 := by
  induction d with
  | zero => exact fun V _ _ _ f h => ⟨Module.finBasisOfFinrankEq ℂ V h, fun i => i.elim0⟩
  | succ d ih =>
    intro V _ _ _ f h
    haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
    have h1 : LinearMap.range (f - μ • (1 : Module.End ℂ V)) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, ← LinearMap.ker_eq_bot_iff_range_eq_top]
      rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def] at hμ
      exact hμ
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ h1
    have hk : Module.finrank ℂ (LinearMap.ker φ) = d := by
      have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
      omega
    have hm : ∀ x ∈ LinearMap.ker φ, f x ∈ LinearMap.ker φ := fun x hx => by
      have := (LinearMap.ker φ).add_mem (hle ⟨x, rfl⟩) ((LinearMap.ker φ).smul_mem μ hx)
      simpa using this
    obtain ⟨b, hb⟩ := ih _ (f.restrict hm) hk
    obtain ⟨y, hy⟩ : ∃ y, φ y = 1 := LinearMap.surjective_of_ne_zero hφ 1
    let b' := Module.Basis.mkFinCons y b (fun c x hx h => by
      have := congrArg φ h
      rwa [map_add, map_smul, hy, LinearMap.mem_ker.1 hx, map_zero, add_zero, smul_eq_mul, mul_one] at this)
      (fun z => ⟨-φ z, by simp [hy]⟩)
    have hb' : ∀ i, b' (Fin.succ i) = b i := fun i => by simp [b']
    refine ⟨b', fun i j hij => ?_⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij))
    have e : f (b' j.succ) = ∑ k, b.repr (f.restrict hm (b j)) k • b' k.succ := by
      have := congrArg Subtype.val (b.sum_repr (f.restrict hm (b j)))
      rw [hb']
      simp only [hb']
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [e, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with hk
    · rw [hb k j (by rw [← hk] at hij; exact Fin.succ_lt_succ_iff.1 hij), zero_smul]
    · simp

private theorem tri_mat {d : ℕ} (g : GL (Fin d) ℂ) : ∃ Q : GL (Fin d) ℂ, ∀ i j, i < j → (Q⁻¹ * g * Q : GL (Fin d) ℂ) i j = 0 := by
  obtain ⟨b, hb⟩ := tri d (Fin d → ℂ) (Matrix.toLin' (g : Matrix (Fin d) (Fin d) ℂ)) (by simp)
  let e := Pi.basisFun ℂ (Fin d)
  refine ⟨⟨e.toMatrix b, b.toMatrix e, e.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip e⟩, fun i j h => ?_⟩
  have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b e b e (Matrix.toLin' (g : Matrix (Fin d) (Fin d) ℂ))
  rw [show LinearMap.toMatrix e e (Matrix.toLin' (g : Matrix (Fin d) (Fin d) ℂ)) = g by simp [e]] at this
  change (b.toMatrix e * (g : Matrix (Fin d) (Fin d) ℂ) * e.toMatrix b) i j = 0
  rw [this, LinearMap.toMatrix_apply, hb i j h]

private theorem homogeneous_trace_conj {d : ℕ} (n : ℕ) (g Q : GL (Fin d) ℂ) : tr1 d n (Q⁻¹ * g * Q) = tr1 d n g := by
  haveI := finMH Unit d fun _ => n
  have e : ∀ a b : GL (Fin d) ℂ, mRep d (fun _ : Unit => n) (fun _ => a * b) = mRep d _ (fun _ => a) * mRep d _ fun _ => b :=
    fun a b => by rw [← map_mul]; rfl
  unfold tr1
  rw [e, LinearMap.trace_mul_comm, ← e, ← mul_assoc, mul_inv_cancel, one_mul]

open MvPolynomial in
private theorem cont_coeff {σ ι : Type} [Fintype ι] (F : ι → ℂ → MvPolynomial σ ℂ) (h : ∀ i m, Continuous fun t => coeff m (F i t))
    (s : Multiset ι) : ∀ m, Continuous fun t => coeff m (s.map fun i => F i t).prod := by
  classical
  induction s using Multiset.induction_on with
  | empty => exact fun m => continuous_const
  | cons a s ih =>
    intro m
    simp only [Multiset.map_cons, Multiset.prod_cons, MvPolynomial.coeff_mul]
    exact continuous_finset_sum _ fun p _ => (h a _).mul (ih _)

open MvPolynomial in
private theorem homogeneous_trace_diagonal {d : ℕ} (n : ℕ) (g : GL (Fin d) ℂ) (h : ∀ i j, i ≠ j → g i j = 0) :
    tr1 d n g = MvPolynomial.eval (fun i => g i i) (hsymm (Fin d) ℂ n) := by
  classical
  have e : ∀ m : Unit × Fin d →₀ ℕ, coeff m (sbs (fun _ : Unit => g) (MvPolynomial.monomial m 1)) = ∏ i, g i i ^ m ((), i) := fun m => by
    have : sbs (fun _ : Unit => g) (MvPolynomial.monomial m 1) = MvPolynomial.monomial m (∏ i, g i i ^ m ((), i)) := by
      refine MvPolynomial.funext fun x => ?_
      have a : act (fun _ : Unit => g) x = fun p => x p * g p.2 p.2 := funext fun p =>
        Finset.sum_eq_single p.2 (fun j _ hj => by rw [h j _ hj, mul_zero]) (by simp)
      rw [eval_sbs, a, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp),
        Finsupp.prod_fintype _ _ (by simp)]
      simp [Fintype.prod_prod_type, mul_pow, Finset.prod_mul_distrib, mul_comm]
    rw [this, MvPolynomial.coeff_monomial, if_pos rfl]
  rw [symPowTrace_eq_sum_coeff, hsymm, map_sum]
  simp only [e]
  symm
  refine Finset.sum_bij (fun s _ => Finsupp.equivFunOnFinite.symm fun p : Unit × Fin d => s.1.count p.2) (fun s _ => mem_homogeneousExponentsOneBlock.2 ?_)
    (fun s _ s' _ hs => Subtype.ext (Multiset.ext' fun a => ?_)) (fun m hm => ?_) fun s _ => ?_
  · exact (Multiset.sum_count_eq_card fun a _ => Finset.mem_univ a).trans s.2
  · exact DFunLike.congr_fun hs ((), a)
  · refine ⟨⟨∑ i, Multiset.replicate (m ((), i)) i, by simpa using mem_homogeneousExponentsOneBlock.1 hm⟩, Finset.mem_univ _, ?_⟩
    ext ⟨⟨⟩, i⟩
    simp [Multiset.count_sum', Multiset.count_replicate]
  · rw [map_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
    simp only [Function.comp_apply, MvPolynomial.eval_X]
    exact Finset.prod_subset (Finset.subset_univ _) fun a _ ha => by
      rw [Multiset.count_eq_zero_of_notMem (by simpa using ha), pow_zero]

private theorem homogeneous_trace_triangular {d : ℕ} (n : ℕ) (g : GL (Fin d) ℂ) (h : ∀ i j, i < j → g i j = 0) :
    tr1 d n g = MvPolynomial.eval (fun i => g i i) (MvPolynomial.hsymm (Fin d) ℂ n) := by
  classical
  let A : ℂ → Matrix (Fin d) (Fin d) ℂ := fun t => Matrix.of fun i j => t ^ ((i : ℕ) - j) * g i j
  have hd : ∀ t, (A t).det ≠ 0 := fun t => by
    have h1 := Matrix.det_of_lowerTriangular (A t) fun i j hij => by simp [A, h i j hij]
    have h2 := Matrix.det_of_lowerTriangular (g : Matrix (Fin d) (Fin d) ℂ) fun i j hij => h i j hij
    rw [h1]
    simpa [A, ← h2] using g.det_ne_zero
  let γ : ℂ → GL (Fin d) ℂ := fun t => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hd t)
  have hc : Continuous fun t => tr1 d n (γ t) := by
    simp only [symPowTrace_eq_sum_coeff]
    refine continuous_finset_sum _ fun m _ => ?_
    have := cont_coeff (fun (p : Unit × Fin d) t => ∑ j, MvPolynomial.X (p.1, j) * MvPolynomial.C (A t j p.2)) (fun p m => by
      simp only [MvPolynomial.coeff_sum, mul_comm (MvPolynomial.X _), MvPolynomial.coeff_C_mul, A, Matrix.of_apply]
      fun_prop) m.toMultiset m
    refine this.congr fun t => ?_
    congr 1
    rw [sbs, MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (by simp) (fun _ _ _ => pow_add _ _ _)]
    rfl
  have h1 : ∀ t ∈ ({0}ᶜ : Set ℂ), tr1 d n (γ t) = tr1 d n g := fun t ht => by
    have ht : t ≠ 0 := ht
    let Q : GL (Fin d) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i : Fin d => t ^ (i : ℕ))
      (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ht)
    rw [← homogeneous_trace_conj n (γ t) Q]
    congr 1
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    refine Units.ext (Matrix.ext fun i j => ?_)
    change (A t * Matrix.diagonal (fun i : Fin d => t ^ (i : ℕ)) : Matrix (Fin d) (Fin d) ℂ) i j =
      (Matrix.diagonal (fun i : Fin d => t ^ (i : ℕ)) * (g : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases lt_or_ge i j with hij | hij
    · simp [A, h i j hij]
    · simp only [A, Matrix.of_apply]
      rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel hij]
  have h2 := congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc continuous_const h1) 0
  rw [← h2, homogeneous_trace_diagonal n (γ 0) fun i j hij => ?_]
  · congr 2
    funext i
    change A 0 i i = _
    simp [A]
  · change A 0 i j = 0
    rcases lt_or_gt_of_ne hij with h' | h'
    · simp [A, h i j h']
    · simp only [A, Matrix.of_apply]
      rw [zero_pow (Nat.sub_ne_zero_of_lt h'), zero_mul]

theorem UpperTheory.V.Z.Sym.Wt.trOne :
    UpperTheory.V.Z.Sym.Wt.TrOne := by
  intro d n g α hα
  classical
  obtain ⟨Q, hQ⟩ := tri_mat g
  rw [← homogeneous_trace_conj n g Q, homogeneous_trace_triangular n _ hQ]
  have h0 : ((Q⁻¹ * g * Q : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly = ∏ i, (X - C (α i)) := by
    rw [← hα, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  generalize Q⁻¹ * g * Q = u at h0 hQ
  obtain ⟨β, hβ⟩ : ∃ β : Fin d → ℂ, β = fun i => u i i := ⟨_, rfl⟩
  rw [← hβ]
  have h1 : ∏ i, (X - C (β i)) = ∏ i, (X - C (α i)) := by
    rw [← h0, ← Matrix.charpoly_transpose, Matrix.charpoly_of_upperTriangular (u : Matrix (Fin d) (Fin d) ℂ).transpose fun i j hij => hQ j i hij, hβ]
    rfl
  have h2 : Finset.univ.val.map β = Finset.univ.val.map α := by
    rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map β), ← roots_multiset_prod_X_sub_C (Finset.univ.val.map α),
      Multiset.map_map, Multiset.map_map]
    exact congrArg roots h1
  have h3 : ∀ c, Fintype.card {i // β i = c} = Fintype.card {i // α i = c} := fun c => by
    have := congrArg (Multiset.count c) h2
    rw [Multiset.count_map, Multiset.count_map] at this
    simp only [Fintype.card_subtype, eq_comm (b := c)]
    exact this
  let e : Fin d ≃ Fin d := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (h3 c)
  have h4 : β = α ∘ e := funext fun i => (Equiv.ofFiberEquiv_map _ i).symm
  rw [h4, ← MvPolynomial.eval_rename, MvPolynomial.rename_hsymm]
