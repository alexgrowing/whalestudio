import Formalism.MahlerMeasure.IsFrozenInv

namespace Formalism.GM.FrozenVariableComponents

open MvPolynomial Finset

section Parts
variable {N r : ℕ}

def ev (N : ℕ) (c : Fin r) : Fin (N + 1) × Fin r := (Fin.last N, c)

noncomputable def llPart (m : Fin (N + 1) × Fin r →₀ ℕ) : Fin N × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => m (Fin.castSucc x.1, x.2))

noncomputable def etaPart (m : Fin (N + 1) × Fin r →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun c => m (Fin.last N, c))

noncomputable def comb (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) : Fin (N + 1) × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => Fin.lastCases (b x.2) (fun i => m (i, x.2)) x.1)

@[simp] theorem llPart_apply (m : Fin (N + 1) × Fin r →₀ ℕ) (x : Fin N × Fin r) :
    llPart m x = m (Fin.castSucc x.1, x.2) := by
  rfl

@[simp] theorem etaPart_apply (m : Fin (N + 1) × Fin r →₀ ℕ) (c : Fin r) :
    etaPart m c = m (Fin.last N, c) := by
  rfl

@[simp] theorem comb_castSucc (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) (i : Fin N) (c : Fin r) :
    comb b m (Fin.castSucc i, c) = m (i, c) := by
  simp [comb]

@[simp] theorem comb_last (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) (c : Fin r) :
    comb b m (Fin.last N, c) = b c := by
  simp [comb]

@[simp] theorem llPart_comb (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) : llPart (comb b m) = m := by
  ext x
  simp

@[simp] theorem etaPart_comb (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) : etaPart (comb b m) = b := by
  ext c
  simp

private theorem fin_castSucc_ne_last (i : Fin N) : Fin.castSucc i ≠ Fin.last N :=
  (Fin.castSucc_lt_last i).ne

private theorem fin_eq_last_or_exists_castSucc (i : Fin (N + 1)) : i = Fin.last N ∨ ∃ j : Fin N, i = Fin.castSucc j := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact Or.inl rfl
  · exact Or.inr ⟨j, rfl⟩

private theorem llPart_add (m m' : Fin (N + 1) × Fin r →₀ ℕ) : llPart (m + m') = llPart m + llPart m' := by
  ext x
  simp

private theorem etaPart_add (m m' : Fin (N + 1) × Fin r →₀ ℕ) :
    etaPart (m + m') = etaPart m + etaPart m' := by
  ext c
  simp

private theorem llPart_tsub (m m' : Fin (N + 1) × Fin r →₀ ℕ) : llPart (m - m') = llPart m - llPart m' := by
  ext x
  simp

private theorem etaPart_tsub (m m' : Fin (N + 1) × Fin r →₀ ℕ) :
    etaPart (m - m') = etaPart m - etaPart m' := by
  ext c
  simp

private theorem llPart_single_castSucc (i : Fin N) (c : Fin r) (k : ℕ) :
    llPart (Finsupp.single (Fin.castSucc i, c) k) = Finsupp.single (i, c) k := by
  ext ⟨i', c'⟩
  simp [Finsupp.single_apply]

private theorem etaPart_single_castSucc (i : Fin N) (c : Fin r) (k : ℕ) :
    etaPart (Finsupp.single (Fin.castSucc i, c) k) = 0 := by
  ext c'
  simp [Finsupp.single_apply, fin_castSucc_ne_last i]

private theorem llPart_single_last (c : Fin r) (k : ℕ) :
    llPart (Finsupp.single (Fin.last N, c) k) = 0 := by
  ext ⟨i', c'⟩
  simp

private theorem etaPart_single_last (c : Fin r) (k : ℕ) :
    etaPart (Finsupp.single (Fin.last N, c) k) = Finsupp.single c k := by
  ext c'
  simp [Finsupp.single_apply]

theorem parts_inj {m m' : Fin (N + 1) × Fin r →₀ ℕ} (h1 : etaPart m = etaPart m')
    (h2 : llPart m = llPart m') : m = m' := by
  ext ⟨i, c⟩
  rcases fin_eq_last_or_exists_castSucc i with rfl | ⟨j, rfl⟩
  · have := DFunLike.congr_fun h1 c
    simpa using this
  · have := DFunLike.congr_fun h2 (j, c)
    simpa using this

theorem comb_parts (m : Fin (N + 1) × Fin r →₀ ℕ) : comb (etaPart m) (llPart m) = m :=
  parts_inj (by simp) (by simp)

end Parts

section Coeff
variable {K : Type*} [CommRing K] {N r : ℕ}

noncomputable def coeffη (b : Fin r →₀ ℕ) :
    MvPolynomial (Fin (N + 1) × Fin r) K →ₗ[K] MvPolynomial (Fin N × Fin r) K :=
  (Finsupp.lsum K (fun m : Fin (N + 1) × Fin r →₀ ℕ =>
    if etaPart m = b then (monomial (llPart m) : K →ₗ[K] MvPolynomial (Fin N × Fin r) K) else 0) :
    ((Fin (N + 1) × Fin r →₀ ℕ) →₀ K) →ₗ[K] MvPolynomial (Fin N × Fin r) K) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

private theorem coeffLinearEquiv_monomial {σ : Type*} (m : σ →₀ ℕ) (a : K) :
    AddMonoidAlgebra.coeffLinearEquiv K (monomial m a : MvPolynomial σ K) = Finsupp.single m a := by
  rfl

private theorem coeffη_eq_lsum (b : Fin r →₀ ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη b F = Finsupp.lsum K (fun m : Fin (N + 1) × Fin r →₀ ℕ =>
      if etaPart m = b then (monomial (llPart m) : K →ₗ[K] MvPolynomial (Fin N × Fin r) K) else 0)
      (AddMonoidAlgebra.coeffLinearEquiv K F) := rfl

theorem coeffη_monomial (b : Fin r →₀ ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ) (a : K) :
    coeffη b (monomial m a) = if etaPart m = b then monomial (llPart m) a else 0 := by
  rw [coeffη_eq_lsum, coeffLinearEquiv_monomial, Finsupp.lsum_single]
  by_cases h : etaPart m = b <;> simp [h]

private theorem coeff_coeffη_eq_coeff_comb (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeff m (coeffη b F) = coeff (comb b m) F := by
  refine MvPolynomial.induction_on' F (fun n a => ?_) (fun p q hp hq => ?_)
  · rw [coeffη_monomial]
    by_cases h : etaPart n = b
    · have key : llPart n = m ↔ n = comb b m :=
        ⟨fun h' => by rw [← h, ← h', comb_parts],
         fun h' => by rw [h', llPart_comb]⟩
      rw [if_pos h, coeff_monomial, coeff_monomial]
      exact if_congr key rfl rfl
    · rw [if_neg h, coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact h (etaPart_comb b m)
  · simp only [map_add, coeff_add, hp, hq]

theorem coeff_coeffη (m : Fin (N + 1) × Fin r →₀ ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeff (llPart m) (coeffη (etaPart m) F) = coeff m F := by
  rw [coeff_coeffη_eq_coeff_comb, comb_parts]

theorem coeff_coeffη' (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeff m (coeffη b F) = coeff (comb b m) F :=
  coeff_coeffη_eq_coeff_comb b m F

end Coeff

end Formalism.GM.FrozenVariableComponents

namespace Formalism.GM.FrozenVariableComponents

open MvPolynomial Finset

section Coeff2
variable {K : Type*} [CommRing K] {N r : ℕ}

theorem X_mul_monomial' {σ : Type*} (x : σ) (m : σ →₀ ℕ) (a : K) :
    (X x : MvPolynomial σ K) * monomial m a = monomial (m + Finsupp.single x 1) a := by
  show monomial (Finsupp.single x 1) (1 : K) * monomial m a = _
  rw [monomial_mul, one_mul, add_comm]

theorem X_pow_mul_monomial' {σ : Type*} (x : σ) (k : ℕ) (m : σ →₀ ℕ) (a : K) :
    (X x : MvPolynomial σ K) ^ k * monomial m a = monomial (m + Finsupp.single x k) a := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul, add_comm]

theorem coeffη_X_castSucc_mul (b : Fin r →₀ ℕ) (i : Fin N) (c : Fin r)
    (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη b (X (Fin.castSucc i, c) * G) = X (i, c) * coeffη b G := by
  refine MvPolynomial.induction_on' G (fun n a => ?_) (fun p q hp hq => ?_)
  · rw [X_mul_monomial', coeffη_monomial, coeffη_monomial, etaPart_add,
      etaPart_single_castSucc, add_zero, llPart_add, llPart_single_castSucc]
    split_ifs <;> simp [X_mul_monomial']
  · simp only [mul_add, map_add, hp, hq]

theorem coeffη_pderiv_castSucc (b : Fin r →₀ ℕ) (i : Fin N) (c : Fin r)
    (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη b (pderiv (Fin.castSucc i, c) G) = pderiv (i, c) (coeffη b G) := by
  refine MvPolynomial.induction_on' G (fun n a => ?_) (fun p q hp hq => ?_)
  · rw [pderiv_monomial, coeffη_monomial, coeffη_monomial, etaPart_tsub,
      etaPart_single_castSucc, tsub_zero, llPart_tsub, llPart_single_castSucc]
    split_ifs <;> simp [pderiv_monomial]
  · simp only [map_add, hp, hq]

theorem coeffη_Xlast_pow_mul_monomial (b : Fin r →₀ ℕ) (ρ : Fin r) (k : ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ)
    (a : K) :
    coeffη b (X (Fin.last N, ρ) ^ k * monomial m a) =
      if etaPart m + Finsupp.single ρ k = b then monomial (llPart m) a else 0 := by
  rw [X_pow_mul_monomial', coeffη_monomial, etaPart_add, llPart_add, etaPart_single_last,
    llPart_single_last, add_zero]

theorem coeffη_shift (b : Fin r →₀ ℕ) (ρ : Fin r) (k : ℕ) (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη (b + Finsupp.single ρ k) (X (Fin.last N, ρ) ^ k * G) = coeffη b G := by
  refine MvPolynomial.induction_on' G (fun n a => ?_) (fun p q hp hq => ?_)
  · rw [coeffη_Xlast_pow_mul_monomial, coeffη_monomial]
    simp only [add_left_inj]
  · simp only [mul_add, map_add, hp, hq]

theorem coeffη_shift_zero (b : Fin r →₀ ℕ) (ρ : Fin r) (k : ℕ) (hb : ¬ Finsupp.single ρ k ≤ b)
    (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη b (X (Fin.last N, ρ) ^ k * G) = 0 := by
  refine MvPolynomial.induction_on' G (fun n a => ?_) (fun p q hp hq => ?_)
  · rw [coeffη_Xlast_pow_mul_monomial, if_neg]
    intro h
    exact hb (by rw [← h]; exact le_add_self)
  · simp only [mul_add, map_add, hp, hq, add_zero]

theorem coeffη_pderiv_last (b : Fin r →₀ ℕ) (c : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη b (pderiv (Fin.last N, c) G) = ((b c + 1 : ℕ) : K) • coeffη (b + Finsupp.single c 1) G := by
  refine MvPolynomial.induction_on' G (fun n a => ?_) (fun p q hp hq => ?_)
  · rw [pderiv_monomial, coeffη_monomial, coeffη_monomial, etaPart_tsub, etaPart_single_last,
      llPart_tsub, llPart_single_last, tsub_zero]
    by_cases h1 : etaPart n = b + Finsupp.single c 1
    · have hc : n (Fin.last N, c) = b c + 1 := by
        have := DFunLike.congr_fun h1 c
        simpa using this
      rw [if_pos h1, if_pos (show etaPart n - Finsupp.single c 1 = b by rw [h1, add_tsub_cancel_right]),
        smul_monomial, hc, smul_eq_mul, mul_comm]
    · rw [if_neg h1, smul_zero]
      split_ifs with h2
      · by_cases h3 : n (Fin.last N, c) = 0
        · simp [h3]
        · exfalso
          apply h1
          have hle : Finsupp.single c 1 ≤ etaPart n := by
            rw [Finsupp.single_le_iff, etaPart_apply]
            omega
          rw [← h2, tsub_add_cancel_of_le hle]
      · rfl
  · simp only [map_add, smul_add, hp, hq]

end Coeff2

end Formalism.GM.FrozenVariableComponents

namespace Formalism.GM.FrozenVariableComponents

open MvPolynomial Finset Formalism.GM.M

section Gl
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem glAct_apply (LL : Letters N) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d F = ∑ i : Fin N, if (i : ℕ) < j then
      (if LL.vec i then X (i, c) * pderiv (i, d) F else -(X (i, d) * pderiv (i, c) F)) else 0 := by
  unfold Formalism.GM.M.glAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

theorem snoc_vec_castSucc (LL : Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).vec (Fin.castSucc i) = LL.vec i := by
  simp [Formalism.GM.M.Letters.snoc]

theorem snoc_vec_last (LL : Letters N) (n : ℕ) : (LL.snoc n).vec (Fin.last N) = false := by
  simp [Formalism.GM.M.Letters.snoc]

theorem snoc_deg_castSucc (LL : Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).deg (Fin.castSucc i) = LL.deg i := by
  simp [Formalism.GM.M.Letters.snoc]

theorem snoc_deg_last (LL : Letters N) (n : ℕ) : (LL.snoc n).deg (Fin.last N) = n := by
  simp [Formalism.GM.M.Letters.snoc]

theorem coeffη_glAct (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (c d : Fin r) (b : Fin r →₀ ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    coeffη b (glAct p (LL.snoc n) j c d F) = glAct p LL j c d (coeffη b F) := by
  rw [glAct_apply, glAct_apply, Fin.sum_univ_castSucc, map_add, map_sum,
    if_neg (show ¬ ((Fin.last N : ℕ) < j) by rw [Fin.val_last]; omega), map_zero, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.coe_castSucc, snoc_vec_castSucc]
  split_ifs <;> simp [coeffη_X_castSucc_mul, coeffη_pderiv_castSucc]

theorem wt_snoc (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (c : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) :
    wt (LL.snoc n) j c m = wt LL j c (llPart m) := by
  unfold Formalism.GM.M.wt
  rw [Fin.sum_univ_castSucc, if_neg (show ¬ ((Fin.last N : ℕ) < j) by rw [Fin.val_last]; omega), add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.coe_castSucc, snoc_vec_castSucc, llPart_apply]

variable [NeZero r]

private theorem map_mem_sSup_of_forall_mapsTo {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (f : V →ₗ[R] V) (S : Set (Submodule R V)) (h : ∀ T ∈ S, ∀ x ∈ T, f x ∈ T) :
    ∀ x ∈ sSup S, f x ∈ sSup S := by
  have key : sSup S ≤ (sSup S).comap f :=
    sSup_le (fun T hT y hy => (le_sSup hT : T ≤ sSup S) (h T hT y hy))
  exact fun x hx => key hx

theorem ycond_stable (LL : Letters N) (j : ℕ) (M : WithTop ℤ) : GlStable p LL j (YCond p (r := r) LL j M) := by
  intro c d x hx
  unfold Formalism.GM.M.YCond at hx ⊢
  exact map_mem_sSup_of_forall_mapsTo (Formalism.GM.M.glAct p LL j c d) _ (fun T hT => hT.2 c d) x hx

theorem ycond_le (LL : Letters N) (j : ℕ) (M : WithTop ℤ) :
    YCond p (r := r) LL j M ≤ MvPolynomial.restrictSupport ℚ_[p]
        {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M} := by
  unfold Formalism.GM.M.YCond
  exact sSup_le (fun T hT => hT.1)

theorem wt_le_of_mem (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (F : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hF : F ∈ YCond p LL j M) (m : Fin N × Fin r →₀ ℕ) (hm : m ∈ F.support) :
    ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M := by
  have h := ycond_le p LL j M hF
  rw [mem_restrictSupport_iff] at h
  exact h (Finset.mem_coe.2 hm)

theorem ycond_map {NA NB : ℕ} (LA : Letters NA) (LB : Letters NB) (jA jB : ℕ) (M : WithTop ℤ)
    (P : MvPolynomial (Fin NA × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin NB × Fin r) ℚ_[p])
    (hc : ∀ c d F, P (glAct p LA jA c d F) = glAct p LB jB c d (P F))
    (hs : ∀ F, ∀ m ∈ (P F).support, ∃ m0 ∈ F.support, wt LB jB 0 m = wt LA jA 0 m0) :
    ∀ F ∈ YCond p LA jA M, P F ∈ YCond p LB jB M := by
  intro F hF
  have hS : Submodule.map P (Formalism.GM.M.YCond p LA jA M) ≤ Formalism.GM.M.YCond p LB jB M := by
    have hmem : Submodule.map P (Formalism.GM.M.YCond p LA jA M) ∈
        {S | S ≤ MvPolynomial.restrictSupport ℚ_[p]
          {m : Fin NB × Fin r →₀ ℕ | ((Formalism.GM.M.wt LB jB 0 m : ℤ) : WithTop ℤ) ≤ M} ∧ Formalism.GM.M.GlStable p LB jB S} := by
      refine ⟨?_, ?_⟩
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
        rw [mem_restrictSupport_iff]
        intro m hm
        obtain ⟨m0, hm0, hw⟩ := hs x m (Finset.mem_coe.1 hm)
        show ((Formalism.GM.M.wt LB jB 0 m : ℤ) : WithTop ℤ) ≤ M
        rw [hw]
        exact wt_le_of_mem p LA jA M x hx m0 hm0
      · intro c d y hy
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
        exact Submodule.mem_map.2 ⟨_, ycond_stable p LA jA M c d x hx, hc c d x⟩
    unfold Formalism.GM.M.YCond
    exact le_sSup hmem
  exact hS (Submodule.mem_map_of_mem hF)

theorem ycond_snoc_fwd (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (M : WithTop ℤ) (b : Fin r →₀ ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hF : F ∈ YCond p (LL.snoc n) j M) :
    coeffη b F ∈ YCond p LL j M := by
  refine ycond_map p (LL.snoc n) LL j j M (coeffη b)
    (fun c d G => coeffη_glAct p LL n j hj c d b G) (fun G m hm => ?_) F hF
  refine ⟨comb b m, ?_, ?_⟩
  · rw [mem_support_iff, ← coeff_coeffη']
    exact mem_support_iff.1 hm
  · rw [wt_snoc LL n j hj, llPart_comb]

theorem ycond_snoc_bwd (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (M : WithTop ℤ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hF : ∀ b, coeffη b F ∈ YCond p LL j M) :
    F ∈ YCond p (LL.snoc n) j M := by
  have hmem : (⨅ b : Fin r →₀ ℕ, (Formalism.GM.M.YCond p LL j M).comap (coeffη b)) ∈
      {S | S ≤ MvPolynomial.restrictSupport ℚ_[p]
        {m : Fin (N + 1) × Fin r →₀ ℕ | ((Formalism.GM.M.wt (LL.snoc n) j 0 m : ℤ) : WithTop ℤ) ≤ M} ∧
        Formalism.GM.M.GlStable p (LL.snoc n) j S} := by
    refine ⟨?_, ?_⟩
    · intro G hG
      rw [mem_restrictSupport_iff]
      intro m hm
      have hG' : coeffη (etaPart m) G ∈ Formalism.GM.M.YCond p LL j M :=
        (Submodule.mem_iInf _).1 hG (etaPart m)
      have hm' : llPart m ∈ (coeffη (etaPart m) G).support := by
        rw [mem_support_iff, coeff_coeffη]
        exact mem_support_iff.1 (Finset.mem_coe.1 hm)
      show ((Formalism.GM.M.wt (LL.snoc n) j 0 m : ℤ) : WithTop ℤ) ≤ M
      rw [wt_snoc LL n j hj]
      exact wt_le_of_mem p LL j M _ hG' _ hm'
    · intro c d G hG
      refine (Submodule.mem_iInf _).2 (fun b => ?_)
      rw [Submodule.mem_comap, coeffη_glAct p LL n j hj c d b G]
      exact ycond_stable p LL j M c d _ ((Submodule.mem_iInf _).1 hG b)
  have hle : (⨅ b : Fin r →₀ ℕ, (Formalism.GM.M.YCond p LL j M).comap (coeffη b)) ≤
      Formalism.GM.M.YCond p (LL.snoc n) j M := by
    unfold Formalism.GM.M.YCond
    exact le_sSup hmem
  exact hle ((Submodule.mem_iInf _).2 (fun b => hF b))

end Gl

end Formalism.GM.FrozenVariableComponents

namespace Formalism.GM.FrozenVariableComponents

open MvPolynomial Finset Formalism.GM.M

section Ops
variable {K : Type*} [CommRing K] {σ : Type*}

theorem X_mul_pderiv_eq_sum [DecidableEq σ] (a b : σ) (F : MvPolynomial σ K) :
    X a * pderiv b F = ∑ m0 ∈ F.support,
      monomial (m0 - Finsupp.single b 1 + Finsupp.single a 1) (coeff m0 F * m0 b) := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m0 _ => ?_)
  rw [pderiv_monomial, X_mul_monomial']

theorem supp_X_mul_pderiv (a b : σ) (F : MvPolynomial σ K) (m : σ →₀ ℕ)
    (hm : m ∈ (X a * pderiv b F).support) :
    ∃ m0 ∈ F.support, ∀ x, x ≠ a → x ≠ b → m x = m0 x := by
  classical
  by_contra hcon
  push Not at hcon
  apply mem_support_iff.1 hm
  rw [X_mul_pderiv_eq_sum, coeff_sum]
  refine Finset.sum_eq_zero (fun m0 hm0 => ?_)
  rw [coeff_monomial, if_neg]
  intro heq
  obtain ⟨x, hxa, hxb, hx⟩ := hcon m0 hm0
  apply hx
  rw [← heq]
  simp [Ne.symm hxa, Ne.symm hxb]

theorem pderiv_comm (a b : σ) (F : MvPolynomial σ K) :
    pderiv a (pderiv b F) = pderiv b (pderiv a F) := by
  classical
  refine MvPolynomial.induction_on' F (fun s c => ?_) (fun p q hp hq => ?_)
  · simp only [pderiv_monomial]
    by_cases hab : a = b
    · subst hab
      rfl
    · rw [show s - Finsupp.single b 1 - Finsupp.single a 1 = s - Finsupp.single a 1 - Finsupp.single b 1 from
        tsub_right_comm]
      congr 1
      rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg hab,
        if_neg (Ne.symm hab), tsub_zero, tsub_zero]
      ring
  · simp only [map_add, hp, hq]

private theorem mvPolynomial_pderiv_X_eq_ite [DecidableEq σ] (x y : σ) :
    pderiv x (X y : MvPolynomial σ K) = if x = y then 1 else 0 := by
  split_ifs with h
  · subst h
    exact pderiv_X_self x
  · exact pderiv_X_of_ne (Ne.symm h)

theorem op_comm (x y x' y' : σ) (h1 : y ≠ x') (h2 : y' ≠ x) (F : MvPolynomial σ K) :
    X x * pderiv y (X x' * pderiv y' F) = X x' * pderiv y' (X x * pderiv y F) := by
  classical
  have e1 : pderiv y (X x' : MvPolynomial σ K) = 0 := by rw [mvPolynomial_pderiv_X_eq_ite, if_neg h1]
  have e2 : pderiv y' (X x : MvPolynomial σ K) = 0 := by rw [mvPolynomial_pderiv_X_eq_ite, if_neg h2]
  simp only [Derivation.leibniz, e1, e2, smul_eq_mul]
  rw [pderiv_comm y y' F]
  ring

private theorem mvPolynomial_pderiv_X_mul_X_eq_ite [DecidableEq σ] (z u v : σ) :
    pderiv z (X u * X v : MvPolynomial σ K) = (if z = v then X u else 0) + (if z = u then X v else 0) := by
  rw [Derivation.leibniz, mvPolynomial_pderiv_X_eq_ite, mvPolynomial_pderiv_X_eq_ite, smul_eq_mul, smul_eq_mul]
  split_ifs <;> simp

private theorem homogeneousComponent_monomial_eq_ite (t : ℕ) (u : σ →₀ ℕ) (a : K) :
    homogeneousComponent t (monomial u a : MvPolynomial σ K) = if t = u.degree then monomial u a else 0 := by
  exact homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial a rfl))

private theorem degree_add_single_one_eq (s : σ →₀ ℕ) (x y : σ) :
    (s + Finsupp.single x 1).degree = (s + Finsupp.single y 1).degree := by
  first
  | simp [Finsupp.degree_add, Finsupp.degree_single]
  | simp [map_add]

theorem op_hc (x y : σ) (t : ℕ) (F : MvPolynomial σ K) :
    homogeneousComponent t (X x * pderiv y F) = X x * pderiv y (homogeneousComponent t F) := by
  classical
  refine MvPolynomial.induction_on' F (fun s c => ?_) (fun p q hp hq => ?_)
  · by_cases hs : s y = 0
    · have h0 : pderiv y (monomial s c : MvPolynomial σ K) = 0 := by
        rw [pderiv_monomial, hs]
        simp
      rw [h0, mul_zero, map_zero, homogeneousComponent_monomial_eq_ite]
      split_ifs
      · rw [h0, mul_zero]
      · simp
    · obtain ⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single y 1 :=
        ⟨s - Finsupp.single y 1,
          (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hs))).symm⟩
      rw [pderiv_monomial, add_tsub_cancel_right, X_mul_monomial', homogeneousComponent_monomial_eq_ite,
        homogeneousComponent_monomial_eq_ite, degree_add_single_one_eq s' x y]
      split_ifs
      · rw [pderiv_monomial, add_tsub_cancel_right, X_mul_monomial']
      · simp
  · simp only [map_add, mul_add, hp, hq]

end Ops

section Rest
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

noncomputable def top (LL : Letters N) (i : Fin N) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  if LL.vec i then (LinearMap.mulLeft ℚ_[p] (X (i, c))) ∘ₗ (pderiv (i, d)).toLinearMap
  else -((LinearMap.mulLeft ℚ_[p] (X (i, d))) ∘ₗ (pderiv (i, c)).toLinearMap)

theorem top_apply (LL : Letters N) (i : Fin N) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    top p LL i c d F = if LL.vec i then X (i, c) * pderiv (i, d) F else -(X (i, d) * pderiv (i, c) F) := by
  unfold top
  split_ifs <;> simp

theorem glAct_eq_top (LL : Letters N) (j : ℕ) (c d : Fin r) :
    glAct p LL j c d = ∑ i : Fin N, if (i : ℕ) < j then top p LL i c d else 0 := rfl

noncomputable def restAct (LL : Letters N) (j : ℕ) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ∑ i : Fin N, if j ≤ (i : ℕ) then top p LL i c d else 0

theorem glAct_full_split (LL : Letters N) (j : ℕ) (c d : Fin r) :
    glAct p LL N c d = glAct p LL j c d + restAct p LL j c d := by
  rw [glAct_eq_top, glAct_eq_top, restAct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [if_pos i.isLt]
  split_ifs with h1 h2 h2
  · exfalso; omega
  · simp
  · simp
  · exfalso; omega

theorem top_comm (LL : Letters N) (i i' : Fin N) (hi : i ≠ i') (c d c' d' : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    top p LL i c d (top p LL i' c' d' F) = top p LL i' c' d' (top p LL i c d F) := by
  have h1 : ∀ a b : Fin r, ((i, a) : Fin N × Fin r) ≠ (i', b) := fun a b h => hi (congrArg Prod.fst h)
  have h2 : ∀ a b : Fin r, ((i', a) : Fin N × Fin r) ≠ (i, b) := fun a b h => hi (congrArg Prod.fst h).symm
  simp only [top_apply]
  split_ifs <;> (try simp only [map_neg, mul_neg, neg_neg, neg_inj]) <;>
    exact op_comm _ _ _ _ (h1 _ _) (h2 _ _) F

theorem rest_comm (LL : Letters N) (j : ℕ) (c d c' d' : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    restAct p LL j c d (glAct p LL j c' d' F) = glAct p LL j c' d' (restAct p LL j c d F) := by
  rw [glAct_eq_top]
  unfold restAct
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  split_ifs <;> (try simp only [LinearMap.zero_apply, map_zero]) <;>
    exact top_comm p LL _ _ (fun h => by subst h; omega) _ _ _ _ F

variable [NeZero r]

private theorem wt_eq_of_eq_away_from_index (LL : Formalism.GM.M.Letters N) (j : ℕ) (i : Fin N) (hij : j ≤ (i : ℕ))
    (m m0 : Fin N × Fin r →₀ ℕ) (c0 : Fin r) (h : ∀ x : Fin N × Fin r, x.1 ≠ i → m x = m0 x) :
    Formalism.GM.M.wt LL j c0 m = Formalism.GM.M.wt LL j c0 m0 := by
  unfold Formalism.GM.M.wt
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  by_cases h1 : (i' : ℕ) < j
  · have e : m (i', c0) = m0 (i', c0) := h _ (fun e => by
      have e' : (i' : ℕ) = i := congrArg Fin.val e
      omega)
    simp only [e]
  · simp [h1]

theorem rest_supp (LL : Letters N) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) (hm : m ∈ (restAct p LL j c d F).support) :
    ∃ m0 ∈ F.support, wt LL j 0 m = wt LL j 0 m0 := by
  classical
  have hsum : ∃ i : Fin N, m ∈ ((if j ≤ (i : ℕ) then top p LL i c d else 0) F).support := by
    by_contra hcon
    push Not at hcon
    apply mem_support_iff.1 hm
    unfold restAct
    rw [LinearMap.sum_apply, coeff_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h := hcon i
    rw [mem_support_iff, not_not] at h
    exact h
  obtain ⟨i, hi⟩ := hsum
  split_ifs at hi with hij
  · rw [top_apply] at hi
    split_ifs at hi with hv
    · obtain ⟨m0, hm0, hx⟩ := supp_X_mul_pderiv _ _ F m hi
      exact ⟨m0, hm0, wt_eq_of_eq_away_from_index LL j i hij m m0 0
        (fun x hx' => hx x (fun e => hx' (by rw [e])) (fun e => hx' (by rw [e])))⟩
    · rw [support_neg] at hi
      obtain ⟨m0, hm0, hx⟩ := supp_X_mul_pderiv _ _ F m hi
      exact ⟨m0, hm0, wt_eq_of_eq_away_from_index LL j i hij m m0 0
        (fun x hx' => hx x (fun e => hx' (by rw [e])) (fun e => hx' (by rw [e])))⟩
  · simp at hi

theorem ycond_full (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (c d : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hF : F ∈ YCond p LL j M) :
    glAct p LL N c d F ∈ YCond p LL j M := by
  rw [glAct_full_split p LL j c d, LinearMap.add_apply]
  exact add_mem (ycond_stable p LL j M c d F hF)
    (ycond_map p LL LL j j M (restAct p LL j c d)
      (fun c' d' G => rest_comm p LL j c d c' d' G)
      (fun G m hm => rest_supp p LL j c d G m hm) F hF)

theorem ycond_hc (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (t : ℕ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hF : F ∈ YCond p LL j M) :
    homogeneousComponent t F ∈ YCond p LL j M := by
  refine ycond_map p LL LL j j M (homogeneousComponent t) (fun c d G => ?_) (fun G m hm => ?_) F hF
  · rw [glAct_apply, glAct_apply, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp [op_hc]
  · have h := mem_support_iff.1 hm
    rw [coeff_homogeneousComponent] at h
    split_ifs at h
    · exact ⟨m, mem_support_iff.2 h, rfl⟩
    · exact absurd rfl h

end Rest

end Formalism.GM.FrozenVariableComponents

namespace Formalism.GM.FrozenVariableComponents

open MvPolynomial Finset Formalism.GM.M

section Freeze
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem glAct_full_mul (LL : Letters N) (c d : Fin r) (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL N c d (F * G) = F * glAct p LL N c d G + G * glAct p LL N c d F := by
  simp only [glAct_apply, Derivation.leibniz, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> ring

theorem glAct_full_C (LL : Letters N) (c d : Fin r) (a : ℚ_[p]) : glAct p LL N c d (C a) = 0 := by
  simp [glAct_apply]

theorem glAct_full_X (LL : Letters N) (c ρ : Fin r) (b : Fin N) (d : Fin r) :
    glAct p LL N c ρ (X (b, d)) =
      if LL.vec b then (if d = ρ then X (b, c) else 0) else (if d = c then -X (b, ρ) else 0) := by
  rw [glAct_apply, Finset.sum_eq_single b]
  · rw [if_pos b.isLt]
    cases hv : LL.vec b
    · by_cases h2 : d = c
      · subst h2
        simp
      · simp [h2]
    · by_cases h1 : d = ρ
      · subst h1
        simp
      · simp [h1]
  · intro i _ hib
    simp [hib]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem freezeSub_apply (LL : Letters N) (ρ : Fin r) (i : Fin N) (c : Fin r) :
    freezeSub p LL ρ (i, c) =
    if LL.vec i then
      (if c = ρ then ∑ c', X (Fin.castSucc i, c') * X (Fin.last N, c')
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c))
    else
      (if c = ρ then X (Fin.last N, ρ) * X (Fin.castSucc i, ρ)
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c) - X (Fin.castSucc i, ρ) * X (Fin.last N, c)) := rfl

theorem diff_gen (LL : Letters N) (ρ c : Fin r) (hc : c ≠ ρ) (x : Fin N × Fin r) :
    X (Fin.last N, ρ) * pderiv (Fin.last N, c) (freezeSub p LL ρ x) =
      aeval (freezeSub p LL ρ) (glAct p LL N c ρ (X x)) := by
  obtain ⟨b, d⟩ := x
  have n1 : Fin.last N ≠ Fin.castSucc b := (fin_castSucc_ne_last b).symm
  rw [glAct_full_X, freezeSub_apply]
  split_ifs <;> (try (exfalso; exact hc ((‹d = c›).symm.trans ‹d = ρ›))) <;>
    (try (have hcd : c ≠ d := Ne.symm ‹¬d = c›)) <;>
    (try (have hρd : ρ ≠ d := Ne.symm ‹¬d = ρ›)) <;>
    simp only [map_sub, map_sum, map_neg, map_zero, mvPolynomial_pderiv_X_mul_X_eq_ite] <;>
    simp [*, n1, Ne.symm hc, freezeSub_apply, Finset.sum_ite_eq, Finset.sum_ite_eq'] <;> ring

theorem diff_id (LL : Letters N) (ρ c : Fin r) (hc : c ≠ ρ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    X (Fin.last N, ρ) * pderiv (Fin.last N, c) (aeval (freezeSub p LL ρ) f) =
      aeval (freezeSub p LL ρ) (glAct p LL N c ρ f) := by
  induction f using MvPolynomial.induction_on
  · rename_i a
    rw [glAct_full_C, map_zero, aeval_C]
    simp
  · rename_i f g hf hg
    simp only [map_add, mul_add, hf, hg]
  · rename_i f x hf
    have e1 := diff_gen p LL ρ c hc x
    rw [map_mul (aeval (Formalism.GM.M.freezeSub p LL ρ)) f (X x), Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      glAct_full_mul, map_add (aeval (Formalism.GM.M.freezeSub p LL ρ)), map_mul (aeval (Formalism.GM.M.freezeSub p LL ρ)),
      map_mul (aeval (Formalism.GM.M.freezeSub p LL ρ)), ← hf, ← e1, aeval_X]
    ring

end Freeze

end Formalism.GM.FrozenVariableComponents

namespace Formalism.GM.FrozenVariableComponents

open MvPolynomial Finset Formalism.GM.M

section Base
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

def emb (x : Fin N × Fin r) : Fin (N + 1) × Fin r := (Fin.castSucc x.1, x.2)

theorem emb_inj : Function.Injective (emb : Fin N × Fin r → Fin (N + 1) × Fin r) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simpa [emb] using h

noncomputable def kill (ρ : Fin r) :
    MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] :=
  aeval (fun w => if w.1 = Fin.last N ∧ w.2 ≠ ρ then 0 else X w)

private theorem kill_monomial_eq_ite (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) (a : ℚ_[p]) :
    kill p ρ (monomial m a) =
      if (∀ c, c ≠ ρ → m (Fin.last N, c) = 0) then monomial m a else 0 := by
  classical
  rw [kill, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, Finsupp.prod, Finsupp.prod]
    refine congrArg (fun z => algebraMap ℚ_[p] (MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) a * z) ?_
    refine Finset.prod_congr rfl (fun w hw => ?_)
    try dsimp only
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply Finsupp.mem_support_iff.1 hw
    have h3 := h w.2 h2
    rw [← h1] at h3
    exact h3
  · push Not at h
    obtain ⟨c, hc, hm⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hm), mul_zero]
    try dsimp only
    have hw : ((Fin.last N, c) : Fin (N + 1) × Fin r).1 = Fin.last N ∧
        ((Fin.last N, c) : Fin (N + 1) × Fin r).2 ≠ ρ := ⟨rfl, hc⟩
    rw [if_pos hw, zero_pow hm]

theorem coeffη_kill (ρ : Fin r) (t : ℕ) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    coeffη (Finsupp.single ρ t) (kill p ρ G) = coeffη (Finsupp.single ρ t) G := by
  refine MvPolynomial.induction_on' G (fun m a => ?_) (fun f g hf hg => ?_)
  · rw [kill_monomial_eq_ite]
    split_ifs with h
    · rfl
    · rw [map_zero, coeffη_monomial, if_neg]
      intro hm
      apply h
      intro c hc
      have := DFunLike.congr_fun hm c
      simpa [Finsupp.single_apply, Ne.symm hc] using this
  · simp only [map_add, hf, hg]

theorem kill_freezeSub (LL : Letters N) (ρ : Fin r) :
    (kill p ρ).comp (aeval (freezeSub p LL ρ)) =
      aeval (fun x : Fin N × Fin r =>
        (X (Fin.last N, ρ) * X (emb x) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, c⟩
  rw [AlgHom.comp_apply, aeval_X, aeval_X, freezeSub_apply]
  have n2 : ∀ i : Fin N, Fin.castSucc i ≠ Fin.last N := fun i => fin_castSucc_ne_last i
  cases hv : LL.vec i <;> by_cases hc : c = ρ <;>
    simp [kill, emb, hc, n2, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq'] <;> ring

theorem aeval_scaled_monomial (ρ : Fin r) (m : Fin N × Fin r →₀ ℕ) (a : ℚ_[p]) :
    aeval (fun x : Fin N × Fin r => (X (Fin.last N, ρ) * X (emb x) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]))
      (monomial m a) = X (Fin.last N, ρ) ^ m.degree * monomial (Finsupp.mapDomain emb m) a := by
  have h1 : (monomial (Finsupp.mapDomain emb m) a : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) =
      algebraMap ℚ_[p] (MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) a *
        m.prod (fun x k => (X (emb x) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) ^ k) := by
    first
    | rw [monomial_eq, Finsupp.prod_mapDomain_index_inj emb_inj, MvPolynomial.algebraMap_eq]
    | rw [monomial_eq, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
        MvPolynomial.algebraMap_eq]
    | (rw [← rename_monomial]
       show aeval (fun i => (X (emb i) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])) (monomial m a) = _
       rw [aeval_monomial])
    all_goals rfl
  have hdeg : m.degree = ∑ i ∈ m.support, m i := by
    first
    | rfl
    | simp [Finsupp.degree]
    | exact Finsupp.degree_eq_sum m
  rw [aeval_monomial, h1]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hdeg]
  ring

private theorem llPart_mapDomain_emb (m : Fin N × Fin r →₀ ℕ) :
    llPart (Finsupp.mapDomain emb m) = m := by
  ext ⟨i, c⟩
  rw [llPart_apply]
  exact Finsupp.mapDomain_apply emb_inj m (i, c)

private theorem etaPart_mapDomain_emb (m : Fin N × Fin r →₀ ℕ) :
    etaPart (Finsupp.mapDomain emb m) = 0 := by
  ext c
  rw [etaPart_apply]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨⟨i, c'⟩, h⟩
  simp [emb, fin_castSucc_ne_last i] at h

theorem coeffη_base (LL : Letters N) (ρ : Fin r) (t : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    coeffη (Finsupp.single ρ t) (aeval (freezeSub p LL ρ) f) = homogeneousComponent t f := by
  rw [← coeffη_kill,
    show kill p ρ (aeval (Formalism.GM.M.freezeSub p LL ρ) f) =
      ((kill p ρ).comp (aeval (Formalism.GM.M.freezeSub p LL ρ))) f from rfl,
    kill_freezeSub]
  refine MvPolynomial.induction_on' f (fun m a => ?_) (fun f g hf hg => ?_)
  · rw [aeval_scaled_monomial, coeffη_Xlast_pow_mul_monomial, etaPart_mapDomain_emb,
      llPart_mapDomain_emb, zero_add, homogeneousComponent_monomial_eq_ite]
    have key : (Finsupp.single ρ m.degree = Finsupp.single ρ t) ↔ t = m.degree :=
      ⟨fun h' => (Finsupp.single_injective ρ h').symm, fun h' => by rw [h']⟩
    exact if_congr key rfl rfl
  · simp only [map_add, hf, hg]

variable [NeZero r]

theorem freeze_coeff_mem (LL : Letters N) (ρ : Fin r) (j : ℕ) (M : WithTop ℤ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : f ∈ YCond p LL j M) (b : Fin r →₀ ℕ) :
    coeffη b (aeval (freezeSub p LL ρ) f) ∈ YCond p LL j M := by
  classical
  suffices H : ∀ n : ℕ, ∀ g ∈ Formalism.GM.M.YCond p LL j M, ∀ b' : Fin r →₀ ℕ,
      (∑ c ∈ Finset.univ.erase ρ, b' c) = n →
      coeffη b' (aeval (Formalism.GM.M.freezeSub p LL ρ) g) ∈ Formalism.GM.M.YCond p LL j M by
    exact H _ f hf b rfl
  intro n
  induction n with
  | zero =>
    intro g hg b' hb
    have hb' : b' = Finsupp.single ρ (b' ρ) := by
      ext c
      by_cases hc : c = ρ
      · subst hc
        simp
      · rw [Finsupp.single_apply, if_neg (Ne.symm hc)]
        exact (Finset.sum_eq_zero_iff.1 hb) c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩)
    rw [hb', coeffη_base]
    exact ycond_hc p LL j M _ g hg
  | succ n ih =>
    intro g hg b' hb
    obtain ⟨c, hc, hbc⟩ : ∃ c ∈ Finset.univ.erase ρ, b' c ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [Finset.sum_eq_zero hcon] at hb
      exact Nat.succ_ne_zero n hb.symm
    have hcρ : c ≠ ρ := (Finset.mem_erase.1 hc).1
    obtain ⟨b0, rfl⟩ : ∃ b0, b' = b0 + Finsupp.single c 1 :=
      ⟨b' - Finsupp.single c 1,
        (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hbc))).symm⟩
    have e1 : ∑ c' ∈ Finset.univ.erase ρ, (b0 + Finsupp.single ρ 1 : Fin r →₀ ℕ) c' = ∑ c' ∈ Finset.univ.erase ρ, b0 c' :=
      Finset.sum_congr rfl (fun c' hc' => by
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.mem_erase.1 hc').1), add_zero])
    have e3 : ∑ c' ∈ Finset.univ.erase ρ, (Finsupp.single c 1 : Fin r →₀ ℕ) c' = 1 := by
      rw [Finset.sum_eq_single c (fun c' _ hc' => by rw [Finsupp.single_apply, if_neg (Ne.symm hc')])
          (fun h => absurd hc h), Finsupp.single_eq_same]
    have e2 : ∑ c' ∈ Finset.univ.erase ρ, (b0 + Finsupp.single c 1 : Fin r →₀ ℕ) c' =
        ∑ c' ∈ Finset.univ.erase ρ, b0 c' + 1 := by
      rw [Finset.sum_congr rfl (fun c' _ => Finsupp.add_apply b0 (Finsupp.single c 1) c'), Finset.sum_add_distrib, e3]
    have hs : ∑ c' ∈ Finset.univ.erase ρ, (b0 + Finsupp.single ρ 1 : Fin r →₀ ℕ) c' = n := by
      rw [e1]
      omega
    have key := ih _ (ycond_full p LL j M c ρ g hg) (b0 + Finsupp.single ρ 1) hs
    rw [← diff_id p LL ρ c hcρ g, ← pow_one (X (Fin.last N, ρ) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
      coeffη_shift, coeffη_pderiv_last] at key
    have hne : ((b0 c + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
    have h2 := Submodule.smul_mem _ ((b0 c + 1 : ℕ) : ℚ_[p])⁻¹ key
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2

end Base

end Formalism.GM.FrozenVariableComponents

namespace Formalism.GM.FrozenVariableComponents

open MvPolynomial Finset Formalism.GM.M

section Pol
variable {K : Type*} [CommRing K]

private theorem isWeightedHomogeneous_finset_sum {τ ι : Type*} {w : τ → ℕ} (s : Finset ι) (φ : ι → MvPolynomial τ K) {n : ℕ}
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) n) : IsWeightedHomogeneous w (∑ i ∈ s, φ i) n := by
  intro d hd
  rw [coeff_sum] at hd
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  exact h i hi hne

private theorem isWeightedHomogeneous_of_eq_deg {τ : Type*} {w : τ → ℕ} {φ : MvPolynomial τ K} {a b : ℕ}
    (h : IsWeightedHomogeneous w φ a) (e : a = b) : IsWeightedHomogeneous w φ b := e ▸ h

private theorem isWeightedHomogeneous_one' {τ : Type*} (w : τ → ℕ) : IsWeightedHomogeneous w (1 : MvPolynomial τ K) 0 := by
  first
  | exact isWeightedHomogeneous_one w
  | exact isWeightedHomogeneous_one _ w
  | (intro d hd
     rw [coeff_one] at hd
     split_ifs at hd with h0
     · subst h0
       simp
     · exact absurd rfl hd)

private theorem isWeightedHomogeneous_pow {τ : Type*} (w : τ → ℕ) (φ : MvPolynomial τ K) (n : ℕ)
    (h : IsWeightedHomogeneous w φ n) (k : ℕ) : IsWeightedHomogeneous w (φ ^ k) (k * n) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_mul]
    exact isWeightedHomogeneous_one' w
  | succ k ih =>
    rw [pow_succ, add_one_mul]
    exact ih.mul h

private theorem isWeightedHomogeneous_finset_prod {τ ι : Type*} (w : τ → ℕ) (s : Finset ι) (φ : ι → MvPolynomial τ K) (n : ι → ℕ)
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) (n i)) :
    IsWeightedHomogeneous w (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact isWeightedHomogeneous_one' w
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem hom_aeval {σ τ : Type*} (w : τ → ℕ) (v : σ → ℕ) (g : σ → MvPolynomial τ K)
    (hg : ∀ x, IsWeightedHomogeneous w (g x) (v x)) (f : MvPolynomial σ K) (d : ℕ)
    (hf : IsWeightedHomogeneous v f d) : IsWeightedHomogeneous w (aeval g f) d := by
  classical
  rw [f.as_sum, map_sum]
  refine isWeightedHomogeneous_finset_sum _ _ (fun m hm => ?_)
  show IsWeightedHomogeneous w (aeval g (monomial m (coeff m f))) d
  have hmd : Finsupp.weight v m = d := hf (mem_support_iff.1 hm)
  have h1 := (isWeightedHomogeneous_C w (coeff m f)).mul
    (isWeightedHomogeneous_finset_prod w m.support (fun x => g x ^ m x) (fun x => m x * v x) (fun x _ => isWeightedHomogeneous_pow w (g x) (v x) (hg x) (m x)))
  have e : 0 + ∑ x ∈ m.support, m x * v x = d := by
    first
    | (rw [zero_add, ← hmd, Finsupp.weight_apply, Finsupp.sum]; simp only [smul_eq_mul])
    | simp [← hmd, Finsupp.weight_apply, Finsupp.sum]
  rw [aeval_monomial, Finsupp.prod]
  exact isWeightedHomogeneous_of_eq_deg h1 e

theorem weight_row {N r : ℕ} (i' : Fin N) (m : Fin N × Fin r →₀ ℕ) :
    Finsupp.weight (fun x : Fin N × Fin r => if x.1 = i' then 1 else 0) m = ∑ c, m (i', c) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single i']
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro i
    simp

private theorem isWeightedHomogeneous_sub {τ : Type*} {w : τ → ℕ} {φ ψ : MvPolynomial τ K} {n : ℕ}
    (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ - ψ) n := by
  intro d hd
  rw [coeff_sub] at hd
  by_cases h1 : coeff d φ = 0
  · rw [h1, zero_sub, neg_ne_zero] at hd
    exact hψ hd
  · exact hφ h1

private theorem isWeightedHomogeneous_X' {τ : Type*} (w : τ → ℕ) (a : τ) : IsWeightedHomogeneous w (X a : MvPolynomial τ K) (w a) := by
  first
  | exact isWeightedHomogeneous_X K w a
  | exact isWeightedHomogeneous_X w a
  | exact isWeightedHomogeneous_X _ w a

theorem weight_one' {N r : ℕ} (m : Fin N × Fin r →₀ ℕ) :
    Finsupp.weight (fun _ : Fin N × Fin r => 1) m = ∑ i, ∑ c, m (i, c) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fintype.sum_prod_type]
    simp
  · intro i
    simp

end Pol

section Pol2
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem hX2 {σ : Type*} (w : σ → ℕ) (a b : σ) (n : ℕ) (h : w a + w b = n) :
    IsWeightedHomogeneous w (X a * X b : MvPolynomial σ ℚ_[p]) n := by
  rw [← h]
  first
  | exact (isWeightedHomogeneous_X ℚ_[p] w a).mul (isWeightedHomogeneous_X ℚ_[p] w b)
  | exact (isWeightedHomogeneous_X w a).mul (isWeightedHomogeneous_X w b)
  | exact (isWeightedHomogeneous_X _ w a).mul (isWeightedHomogeneous_X _ w b)

theorem freezeSub_hom (LL : Letters N) (ρ : Fin r) (i' : Fin (N + 1)) (x : Fin N × Fin r) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => if y.1 = i' then 1 else 0) (freezeSub p LL ρ x)
      ((if Fin.castSucc x.1 = i' then 1 else 0) + (if Fin.last N = i' then 1 else 0)) := by
  obtain ⟨i, c⟩ := x
  rw [freezeSub_apply]
  by_cases hv : LL.vec i = true <;> by_cases hc : c = ρ
  · rw [if_pos hv, if_pos hc]
    exact isWeightedHomogeneous_finset_sum _ _ (fun c' _ => hX2 p _ _ _ _ (by rfl))
  · rw [if_pos hv, if_neg hc]
    exact hX2 p _ _ _ _ (by exact add_comm _ _)
  · rw [if_neg hv, if_pos hc]
    exact hX2 p _ _ _ _ (by exact add_comm _ _)
  · rw [if_neg hv, if_neg hc]
    exact isWeightedHomogeneous_sub (hX2 p _ _ _ _ (by exact add_comm _ _))
      (hX2 p _ _ _ _ (by rfl))

theorem freeze_pol (LL : Letters N) (ρ : Fin r) (n : ℕ) (hn : LL.total ≤ n)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : f ∈ Pol p r LL) :
    freeze p LL ρ n f ∈ Pol p r (LL.snoc n) := by
  unfold Formalism.GM.M.Pol at hf ⊢
  rw [mem_restrictSupport_iff] at hf ⊢
  have hf' : ∀ m ∈ f.support, Formalism.GM.M.MultiDeg LL m := fun m hm => hf (Finset.mem_coe.2 hm)
  have key : ∀ i' : Fin (N + 1), IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => if y.1 = i' then 1 else 0)
      (Formalism.GM.M.freeze p LL ρ n f) ((LL.snoc n).deg i') := by
    intro i'
    unfold Formalism.GM.M.freeze
    rcases fin_eq_last_or_exists_castSucc i' with rfl | ⟨i0, rfl⟩
    · have hfv : IsWeightedHomogeneous (fun x : Fin N × Fin r =>
          (if Fin.castSucc x.1 = Fin.last N then 1 else 0) + (if Fin.last N = Fin.last N then 1 else 0)) f LL.total := by
        intro m hm
        have e : (fun x : Fin N × Fin r =>
            (if Fin.castSucc x.1 = Fin.last N then 1 else 0) + (if Fin.last N = Fin.last N then 1 else 0)) =
            fun _ => 1 := by
          funext x
          simp [fin_castSucc_ne_last]
        rw [e, weight_one']
        unfold Formalism.GM.M.Letters.total
        exact Finset.sum_congr rfl (fun i _ => hf' m (mem_support_iff.2 hm) i)
      have hA := hom_aeval _ _ (Formalism.GM.M.freezeSub p LL ρ)
        (fun x => freezeSub_hom p LL ρ (Fin.last N) x) f _ hfv
      have hX := isWeightedHomogeneous_pow (fun y : Fin (N + 1) × Fin r => if y.1 = Fin.last N then 1 else 0) _ _
        (isWeightedHomogeneous_X' (K := ℚ_[p]) (fun y : Fin (N + 1) × Fin r => if y.1 = Fin.last N then 1 else 0) (Fin.last N, ρ))
        (n - LL.total)
      refine isWeightedHomogeneous_of_eq_deg (hX.mul hA) ?_
      (simp [snoc_deg_last]) <;> omega
    · have hfv : IsWeightedHomogeneous (fun x : Fin N × Fin r =>
          (if Fin.castSucc x.1 = Fin.castSucc i0 then 1 else 0) +
            (if Fin.last N = Fin.castSucc i0 then 1 else 0)) f (LL.deg i0) := by
        intro m hm
        have e : (fun x : Fin N × Fin r =>
            (if Fin.castSucc x.1 = Fin.castSucc i0 then 1 else 0) +
              (if Fin.last N = Fin.castSucc i0 then 1 else 0)) =
            fun x => if x.1 = i0 then 1 else 0 := by
          funext x
          simp [(fin_castSucc_ne_last i0).symm]
        rw [e, weight_row]
        exact hf' m (mem_support_iff.2 hm) i0
      have hA := hom_aeval _ _ (Formalism.GM.M.freezeSub p LL ρ)
        (fun x => freezeSub_hom p LL ρ (Fin.castSucc i0) x) f _ hfv
      have hX := isWeightedHomogeneous_pow (fun y : Fin (N + 1) × Fin r => if y.1 = Fin.castSucc i0 then 1 else 0) _ _
        (isWeightedHomogeneous_X' (K := ℚ_[p]) (fun y : Fin (N + 1) × Fin r => if y.1 = Fin.castSucc i0 then 1 else 0) (Fin.last N, ρ))
        (n - LL.total)
      refine isWeightedHomogeneous_of_eq_deg (hX.mul hA) ?_
      (simp [snoc_deg_castSucc, (fin_castSucc_ne_last i0).symm]) <;> omega
  intro m hm
  show Formalism.GM.M.MultiDeg (LL.snoc n) m
  intro i'
  have h := key i' (mem_support_iff.1 (Finset.mem_coe.1 hm))
  rwa [weight_row] at h

end Pol2

end Formalism.GM.FrozenVariableComponents

namespace Formalism.GM

open MvPolynomial Finset Formalism.GM.M Formalism.GM.FrozenVariableComponents

theorem extendWeightBounded : M.FreezeY := by
  intro p _ N r _ LL ρ n q J Mt hn hJ f hf
  have hf' : ∀ m ∈ f.support, Formalism.GM.M.MultiDeg LL m := by
    intro m hm
    have h := hf
    unfold Formalism.GM.M.Pol at h
    rw [mem_restrictSupport_iff] at h
    exact h (Finset.mem_coe.2 hm)
  have hhom : f.IsHomogeneous LL.total := by
    intro m hm
    show Finsupp.weight (fun _ : Fin N × Fin r => 1) m = LL.total
    rw [Formalism.GM.FrozenVariableComponents.weight_one']
    unfold Formalism.GM.M.Letters.total
    exact Finset.sum_congr rfl (fun i _ => hf' m (mem_support_iff.2 hm) i)
  have hcomp : homogeneousComponent LL.total f = f := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hhom), if_pos rfl]
  have hext := Formalism.GM.FrozenVariableComponents.freeze_pol p LL ρ n hn f hf
  unfold Formalism.GM.M.Y
  simp only [Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨-, hk⟩
    refine ⟨hext, fun k => ?_⟩
    apply Formalism.GM.FrozenVariableComponents.ycond_snoc_bwd p LL n (J k) (hJ k)
    intro b
    by_cases hb : Finsupp.single ρ (n - LL.total) ≤ b
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + Finsupp.single ρ (n - LL.total) :=
        ⟨b - Finsupp.single ρ (n - LL.total), (tsub_add_cancel_of_le hb).symm⟩
      unfold Formalism.GM.M.freeze
      rw [Formalism.GM.FrozenVariableComponents.coeffη_shift]
      exact Formalism.GM.FrozenVariableComponents.freeze_coeff_mem p LL ρ (J k) (Mt k) f (hk k) b'
    · unfold Formalism.GM.M.freeze
      rw [Formalism.GM.FrozenVariableComponents.coeffη_shift_zero b ρ _ hb]
      exact Submodule.zero_mem _
  · rintro ⟨-, hk⟩
    refine ⟨hf, fun k => ?_⟩
    have h1 := Formalism.GM.FrozenVariableComponents.ycond_snoc_fwd p LL n (J k) (hJ k) (Mt k)
      (Finsupp.single ρ LL.total + Finsupp.single ρ (n - LL.total)) _ (hk k)
    unfold Formalism.GM.M.freeze at h1
    rw [Formalism.GM.FrozenVariableComponents.coeffη_shift, Formalism.GM.FrozenVariableComponents.coeffη_base, hcomp] at h1
    exact h1

end Formalism.GM
