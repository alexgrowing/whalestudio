import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

section ItD

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

def itD (f : W → ℂ) (l : List W) (z : W) : ℂ :=
  iteratedFDeriv ℂ l.length f z (fun j => l.get j)

theorem itD_nil (f : W → ℂ) (z : W) : itD f [] z = f z := by
  simp only [itD]
  first
    | exact iteratedFDeriv_zero_apply _
    | simp

theorem itD_differentiable {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (l : List W) :
    Differentiable ℂ (fun y => itD f l y) := by
  have hD : Differentiable ℂ (iteratedFDeriv ℂ l.length f) := by
    refine hf.differentiable_iteratedFDeriv ?_
    first
      | exact_mod_cast ENat.coe_lt_top _
      | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top _)
      | simp
  unfold itD
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l.length => W) ℂ _).differentiable.comp hD

theorem itD_cons {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (e : W) (l : List W) (z : W) :
    itD f (e :: l) z = fderiv ℂ (fun y => itD f l y) z e := by
  have hD : Differentiable ℂ (iteratedFDeriv ℂ l.length f) := by
    refine hf.differentiable_iteratedFDeriv ?_
    first
      | exact_mod_cast ENat.coe_lt_top _
      | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top _)
      | simp
  show iteratedFDeriv ℂ (l.length + 1) f z (fun j => (e :: l).get j) = _
  rw [iteratedFDeriv_succ_apply_left]
  have hc : (fun y => itD f l y) =
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l.length => W) ℂ (fun j => l.get j)) ∘
        iteratedFDeriv ℂ l.length f := rfl
  rw [hc, fderiv_comp z (ContinuousLinearMap.differentiableAt _) (hD z), ContinuousLinearMap.fderiv]
  rfl

theorem fderiv_prod_single {n : ℕ} {h : Fin n → W → ℂ} (hh : ∀ k, Differentiable ℂ (h k))
    (x : Fin n → W) (k0 : Fin n) (e : W) :
    fderiv ℂ (fun y : Fin n → W => ∏ k, h k (y k)) x (Pi.single k0 e) =
      (∏ k ∈ Finset.univ.erase k0, h k (x k)) * fderiv ℂ (h k0) (x k0) e := by
  classical
  have hd : ∀ k, HasFDerivAt (fun y : Fin n → W => h k (y k))
      ((fderiv ℂ (h k) (x k)).comp (ContinuousLinearMap.proj k)) x :=
    fun k => ((hh k) (x k)).hasFDerivAt.comp x (hasFDerivAt_apply k x)
  have hP : HasFDerivAt (fun y : Fin n → W => ∏ k, h k (y k))
      (∑ k, (∏ j ∈ Finset.univ.erase k, h j (x j)) •
        ((fderiv ℂ (h k) (x k)).comp (ContinuousLinearMap.proj k))) x :=
    HasFDerivAt.finset_prod (fun k _ => hd k)
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single k0]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

def colL {n : ℕ} (L : List (Fin n × W)) (k : Fin n) : List W :=
  (L.filter (fun p => p.1 = k)).map Prod.snd

theorem colL_cons {n : ℕ} (a : Fin n × W) (L : List (Fin n × W)) (k : Fin n) :
    colL (a :: L) k = if a.1 = k then a.2 :: colL L k else colL L k := by
  unfold colL
  by_cases h : a.1 = k <;> simp [List.filter_cons, h]

theorem itD_prod {n : ℕ} {g : Fin n → W → ℂ} (hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (g k))
    (L : List (Fin n × W)) (x : Fin n → W) :
    itD (fun v : Fin n → W => ∏ k, g k (v k)) (L.map fun p => Pi.single p.1 p.2) x =
      ∏ k, itD (g k) (colL L k) (x k) := by
  have hP : ContDiff ℂ (⊤ : ℕ∞) (fun v : Fin n → W => ∏ k, g k (v k)) := by
    first
      | exact contDiff_prod fun k _ => (hg k).comp (contDiff_apply ℂ W k)
      | fun_prop
  induction L generalizing x with
  | nil => simp [itD_nil, colL]
  | cons a L ih =>
    simp only [List.map_cons]
    rw [itD_cons hP]
    have hfun : (fun y => itD (fun v : Fin n → W => ∏ k, g k (v k))
        (L.map fun p => Pi.single p.1 p.2) y) = fun y => ∏ k, itD (g k) (colL L k) (y k) :=
      funext fun y => ih y
    rw [hfun, fderiv_prod_single (h := fun k y => itD (g k) (colL L k) y)
      (fun k => itD_differentiable (hg k) _)]
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ a.1)]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      rw [colL_cons, if_neg (Ne.symm (Finset.ne_of_mem_erase hk))]
    · rw [colL_cons, if_pos rfl, itD_cons (hg _)]

theorem itD_col {s : (Fin 1 → W) → ℂ} (hs : ContDiff ℂ (⊤ : ℕ∞) s) (l : List W) :
    itD (fun z : W => s (fun _ => z)) l 0 = iteratedFDeriv ℂ l.length s 0 (fun j _ => l.get j) := by
  unfold itD
  have hi : ((l.length : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    first
      | exact_mod_cast le_top
      | exact WithTop.coe_le_coe.2 le_top
  have h := (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℂ W).iteratedFDeriv_comp_right
    hs (0 : W) hi
  exact congrArg (fun T => T (fun j => l.get j)) h

end ItD

section PD

variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

def pdTerm (u : σ → W) (F : W → ℂ) (x : W) (m : σ →₀ ℕ) : ℂ :=
  iteratedFDeriv ℂ (Multiset.card (Finsupp.toMultiset m)) F x
    (fun k => u ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm)))

theorem polyDeriv_eq_of_subset (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W)
    {S : Finset (σ →₀ ℕ)} (hS : P.support ⊆ S) :
    polyDeriv P u F x = ∑ m ∈ S, P.coeff m * pdTerm u F x m := by
  unfold polyDeriv
  refine Finset.sum_subset hS fun m _ hm => ?_
  first
    | rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]
    | rw [MvPolynomial.not_mem_support_iff.1 hm, zero_mul]

theorem polyDeriv_add (P Q : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (P + Q) u F x = polyDeriv P u F x + polyDeriv Q u F x := by
  classical
  rw [polyDeriv_eq_of_subset (P + Q) u F x (S := P.support ∪ Q.support) MvPolynomial.support_add,
    polyDeriv_eq_of_subset P u F x (S := P.support ∪ Q.support) (fun _ h => Finset.mem_union_left _ h),
    polyDeriv_eq_of_subset Q u F x (S := P.support ∪ Q.support) (fun _ h => Finset.mem_union_right _ h),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem jof_polyDeriv_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ)
    (x : W) : polyDeriv (∑ i ∈ s, P i) u F x = ∑ i ∈ s, polyDeriv (P i) u F x := by
  exact map_sum (AddMonoidHom.mk' (fun Q : MvPolynomial σ ℂ => polyDeriv Q u F x)
    (fun Q R => polyDeriv_add Q R u F x)) P s

theorem polyDeriv_smul (c : ℂ) (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (c • P) u F x = c * polyDeriv P u F x := by
  classical
  rw [polyDeriv_eq_of_subset (c • P) u F x (S := P.support) MvPolynomial.support_smul,
    polyDeriv_eq_of_subset P u F x (S := P.support) subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]

theorem polyDeriv_monomial_one (m : σ →₀ ℕ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (MvPolynomial.monomial m (1 : ℂ)) u F x = pdTerm u F x m := by
  classical
  rw [polyDeriv_eq_of_subset _ u F x (S := {m}) MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, one_mul]

theorem pdTerm_eq_itD (u : σ → W) (F : W → ℂ) (x : W) (m : σ →₀ ℕ) :
    pdTerm u F x m = itD F ((Finsupp.toMultiset m).toList.map u) x := by
  have gen : ∀ (n₁ n₂ : ℕ) (h : n₁ = n₂) (v₁ : Fin n₁ → W) (v₂ : Fin n₂ → W),
      (∀ i, v₁ i = v₂ (i.cast h)) → iteratedFDeriv ℂ n₁ F x v₁ = iteratedFDeriv ℂ n₂ F x v₂ := by
    intro n₁ n₂ h v₁ v₂ hv
    subst h
    exact congrArg _ (funext fun i => hv i)
  unfold pdTerm itD
  refine gen _ _ (by simp) _ _ fun i => ?_
  simp

end PD

end

end ReciprocityTheory.ChartRestriction.G.I2
