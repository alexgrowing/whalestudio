import Formalism.MahlerMeasure.IsFrozenInv

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def evVal (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) :
    Fin (N + 1) × Fin r → MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  fun v => Fin.lastCases (motive := fun _ => MvPolynomial (Fin N × Fin r) ℚ_[p])
    (if v.2 = ρ then 1 else 0) (fun i => X (i, v.2)) v.1

noncomputable def ev (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) :
    MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  aeval (evVal p ρ)

@[simp] lemma evVal_last (ρ c : Fin r) :
    evVal p (N := N) ρ (Fin.last N, c) = if c = ρ then 1 else 0 := by
  simp [evVal]

@[simp] lemma evVal_castSucc (ρ c : Fin r) (i : Fin N) :
    evVal p ρ (Fin.castSucc i, c) = X (i, c) := by
  simp [evVal]

lemma ev_freezeSub (LL : Letters N) (ρ : Fin r) (v : Fin N × Fin r) :
    ev p ρ (freezeSub p LL ρ v) = X v := by
  rcases v with ⟨i, c⟩
  by_cases hv : LL.vec i <;> by_cases hc : c = ρ <;>
    simp [freezeSub, ev, hv, hc, mul_ite, Finset.sum_ite_eq']

lemma ev_freeze (LL : Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ev p ρ (freeze p LL ρ n f) = f := by
  simp only [freeze, map_mul, map_pow]
  have h1 : ev p ρ (X (Fin.last N, ρ)) = 1 := by simp [ev]
  have h2 : ev p ρ (aeval (freezeSub p LL ρ) f) = f := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have : (fun i => (ev p ρ) (freezeSub p LL ρ i)) = X := funext (ev_freezeSub LL ρ)
    rw [this, MvPolynomial.aeval_X_left_apply]
  rw [h1, h2, one_pow, one_mul]

noncomputable def res (m : Fin (N + 1) × Fin r →₀ ℕ) : Fin N × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => m (Fin.castSucc v.1, v.2))

@[simp] lemma res_apply (m : Fin (N + 1) × Fin r →₀ ℕ) (v : Fin N × Fin r) :
    res m v = m (Fin.castSucc v.1, v.2) := by
  simp [res]

noncomputable def ext (n : ℕ) (ρ : Fin r) (m : Fin N × Fin r →₀ ℕ) : Fin (N + 1) × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => Fin.lastCases (motive := fun _ => ℕ)
    (if v.2 = ρ then n else 0) (fun i => m (i, v.2)) v.1)

@[simp] lemma ext_last (n : ℕ) (ρ c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    ext n ρ m (Fin.last N, c) = if c = ρ then n else 0 := by
  simp [ext]

@[simp] lemma ext_castSucc (n : ℕ) (ρ c : Fin r) (m : Fin N × Fin r →₀ ℕ) (i : Fin N) :
    ext n ρ m (Fin.castSucc i, c) = m (i, c) := by
  simp [ext]

@[simp] lemma res_ext (n : ℕ) (ρ : Fin r) (m : Fin N × Fin r →₀ ℕ) : res (ext n ρ m) = m := by
  ext v
  simp

lemma ev_monomial (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) (a : ℚ_[p]) :
    ev p ρ (monomial m a) =
      if (∀ c, c ≠ ρ → m (Fin.last N, c) = 0) then monomial (res m) a else 0 := by
  classical
  rw [ev, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
    Fin.prod_univ_castSucc]
  simp only [evVal_castSucc, evVal_last]
  split_ifs with h
  · have hlast : ∏ c : Fin r, (if c = ρ then (1 : MvPolynomial (Fin N × Fin r) ℚ_[p]) else 0) ^
        m (Fin.last N, c) = 1 := by
      refine Finset.prod_eq_one (fun c _ => ?_)
      by_cases hc : c = ρ
      · simp [hc]
      · simp [hc, h c hc]
    rw [hlast, mul_one, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fintype.prod_prod_type]
    simp only [res_apply, MvPolynomial.algebraMap_eq]
  · push_neg at h
    obtain ⟨c, hc, hc0⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ c) (by simp [hc, hc0]), mul_zero, mul_zero]

lemma coeff_ev (ρ : Fin r) (n : ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hF : ∀ m ∈ F.support, ∑ c, m (Fin.last N, c) = n) (m' : Fin N × Fin r →₀ ℕ) :
    coeff m' (ev p ρ F) = coeff (ext n ρ m') F := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  simp only [ev_monomial]
  rw [Finset.sum_eq_single (ext n ρ m')]
  · rw [if_pos (fun c hc => by rw [ext_last, if_neg hc]), res_ext, MvPolynomial.coeff_monomial, if_pos rfl]
  · intro m hm hne
    split_ifs with hcond
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro hres
      apply hne
      have heq : m = ext n ρ (res m) := by
        ext ⟨i, c⟩
        refine Fin.lastCases ?_ (fun j => ?_) i
        · by_cases hc : c = ρ
          · subst hc
            rw [ext_last, if_pos rfl, ← hF m hm, Finset.sum_eq_single c]
            · intro b _ hb
              exact hcond b hb
            · intro h
              exact absurd (Finset.mem_univ c) h
          · rw [ext_last, if_neg hc, hcond c hc]
        · rw [ext_castSucc, res_apply]
      rw [heq, hres]
    · exact MvPolynomial.coeff_zero _
  · intro hnot
    have h0 : coeff (ext n ρ m') F = 0 := by simpa using hnot
    rw [h0]
    split_ifs <;> simp

end Formalism.GM.M.FB

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

lemma glAct_mul {M : ℕ} (LL : Letters M) (j : ℕ) (c d : Fin r)
    (a b : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    glAct p LL j c d (a * b) = a * glAct p LL j c d b + b * glAct p LL j c d a := by
  simp only [glAct, LinearMap.sum_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Derivation.leibniz, smul_eq_mul] <;> ring

lemma glAct_X {M : ℕ} (LL : Letters M) (c d : Fin r) (j : Fin M) (a : Fin r) :
    glAct p LL M c d (X (j, a)) =
      if LL.vec j then (if a = d then X (j, c) else 0) else (if a = c then -X (j, d) else 0) := by
  simp only [glAct, LinearMap.sum_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hv : LL.vec j <;> by_cases ha : a = d <;> by_cases hc : a = c <;>
      simp [hv, ha, hc, MvPolynomial.pderiv_X, Pi.single_apply, j.isLt] <;> split_ifs <;> simp_all
  · intro i _ hij
    split_ifs <;> simp [MvPolynomial.pderiv_X, Pi.single_apply, Ne.symm hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

@[simp] lemma snoc_vec_last (LL : Letters N) (n : ℕ) : (LL.snoc n).vec (Fin.last N) = false := by
  simp [Letters.snoc]

@[simp] lemma snoc_vec_castSucc (LL : Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).vec (Fin.castSucc i) = LL.vec i := by
  simp [Letters.snoc]

@[simp] lemma snoc_deg_last (LL : Letters N) (n : ℕ) : (LL.snoc n).deg (Fin.last N) = n := by
  simp [Letters.snoc]

@[simp] lemma snoc_deg_castSucc (LL : Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).deg (Fin.castSucc i) = LL.deg i := by
  simp [Letters.snoc]

lemma glAct_freezeSub (LL : Letters N) (n : ℕ) (ρ c : Fin r) (hc : c ≠ ρ) (v : Fin N × Fin r) :
    glAct p (LL.snoc n) (N + 1) c ρ (freezeSub p LL ρ v) = 0 := by
  rcases v with ⟨i, c0⟩
  by_cases hv : LL.vec i <;> by_cases hc0 : c0 = ρ <;>
    simp [freezeSub, hv, hc0, glAct_mul, glAct_X, map_sum, map_sub, Ne.symm hc, hc, mul_ite,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq] <;> ring

lemma glAct_aeval_freezeSub (LL : Letters N) (n : ℕ) (ρ c : Fin r) (hc : c ≠ ρ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p (LL.snoc n) (N + 1) c ρ (aeval (freezeSub p LL ρ) f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h1 : glAct p (LL.snoc n) (N + 1) c ρ (1 : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) = 0 := by
      simp only [glAct, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs <;> simp
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_smul_one, map_smul, h1, smul_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | mul_X f v hf =>
    rw [map_mul, MvPolynomial.aeval_X, glAct_mul, hf, glAct_freezeSub LL n ρ c hc v, mul_zero, mul_zero,
      add_zero]

end Formalism.GM.M.FB

set_option linter.unusedSimpArgs false

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

def wL (N r : ℕ) : Fin (N + 1) × Fin r → ℕ := fun v => if v.1 = Fin.last N then 1 else 0

lemma weight_wL (m : Fin (N + 1) × Fin r →₀ ℕ) :
    Finsupp.weight (wL N r) m = ∑ c, m (Fin.last N, c) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  simp [wL, Fin.castSucc_ne_last]

lemma hom_XX (u v : Fin (N + 1) × Fin r) (h : wL N r u + wL N r v = 1) :
    IsWeightedHomogeneous (wL N r) (X u * X v : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 := by
  have := (MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) u).mul
    (MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) v)
  rwa [h] at this

lemma hom_freezeSub (LL : Letters N) (ρ : Fin r) (v : Fin N × Fin r) :
    IsWeightedHomogeneous (wL N r) (freezeSub p LL ρ v) 1 := by
  rcases v with ⟨i, c⟩
  have hw : ∀ c1 c2, IsWeightedHomogeneous (wL N r)
      (X (Fin.castSucc i, c1) * X (Fin.last N, c2) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 :=
    fun c1 c2 => hom_XX _ _ (by simp [wL, Fin.castSucc_ne_last])
  have hw' : ∀ c1 c2, IsWeightedHomogeneous (wL N r)
      (X (Fin.last N, c2) * X (Fin.castSucc i, c1) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 :=
    fun c1 c2 => hom_XX _ _ (by simp [wL, Fin.castSucc_ne_last])
  simp only [freezeSub]
  split_ifs
  · rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact Submodule.sum_mem _ fun c' _ => (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw c' c')
  · exact hw' c ρ
  · exact hw' ρ ρ
  · rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact Submodule.sub_mem _ ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw' c ρ))
      ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw ρ c))

lemma hom_aeval (LL : Letters N) (ρ : Fin r) (f : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hf : f ∈ Pol p r LL) :
    IsWeightedHomogeneous (wL N r) (aeval (freezeSub p LL ρ) f) LL.total := by
  have hsupp := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hf
  rw [f.as_sum, map_sum, ← MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule, MvPolynomial.aeval_monomial]
  have hdeg : MultiDeg LL m := hsupp (Finset.mem_coe.2 hm)
  have hpr : IsWeightedHomogeneous (wL N r)
      (m.prod fun v k => (freezeSub p LL ρ v) ^ k) (∑ v ∈ m.support, m v • 1) :=
    MvPolynomial.IsWeightedHomogeneous.prod _ _ _
      (fun v _ => (hom_freezeSub LL ρ v).pow (m v))
  have hC := MvPolynomial.isWeightedHomogeneous_C (R := ℚ_[p]) (wL N r) (coeff m f)
  have key := hC.mul hpr
  have hs : ∑ v ∈ m.support, m v • 1 = ∑ v, m v := by
    simp only [smul_eq_mul, mul_one]
    exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simpa using hv)
  convert key using 1
  · rfl
  · rw [hs, zero_add, Fintype.sum_prod_type]
    simp only [Letters.total]
    exact (Finset.sum_congr rfl fun i _ => hdeg i).symm

lemma hom_freeze (LL : Letters N) (ρ : Fin r) (n : ℕ) (hS : LL.total ≤ n)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : f ∈ Pol p r LL) :
    IsWeightedHomogeneous (wL N r) (freeze p LL ρ n f) n := by
  unfold freeze
  have key := ((MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) (Fin.last N, ρ)).pow (n - LL.total)).mul
    (hom_aeval LL ρ f hf)
  convert key using 1
  simp [wL]
  omega

lemma glAct_one (LL : Letters N) (n : ℕ) (ρ c : Fin r) :
    glAct p (LL.snoc n) (N + 1) c ρ (1 : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) = 0 := by
  simp only [glAct, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> simp

lemma freeze_inv (LL : Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsFrozenInv p LL ρ n (freeze p LL ρ n f) := by
  intro c hc
  have hXρ : glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ)) = 0 := by
    rw [glAct_X]
    simp [Ne.symm hc]
  have hpow : ∀ k, glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ) ^ k) = 0 := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact glAct_one LL n ρ c
    | succ k ih => rw [pow_succ, glAct_mul, ih, hXρ, mul_zero, mul_zero, add_zero]
  unfold freeze
  rw [glAct_mul, hpow, glAct_aeval_freezeSub LL n ρ c hc, mul_zero, mul_zero, add_zero]

end Formalism.GM.M.FB

set_option linter.unusedSimpArgs false

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

def kk (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) : ℕ :=
  ∑ c ∈ Finset.univ.erase ρ, m (Fin.last N, c)

lemma coeff_X_pderiv_castSucc (ρ : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hG : ∀ ν : Fin (N + 1) × Fin r →₀ ℕ, kk ρ ν = kk ρ m → coeff ν G = 0)
    (i : Fin N) (a b : Fin r) :
    coeff m (X (Fin.castSucc i, a) * pderiv (Fin.castSucc i, b) G) = 0 := by
  classical
  rw [MvPolynomial.coeff_X_mul']
  split_ifs with h
  · rw [MvPolynomial.coeff_pderiv, hG _ ?_, zero_mul]
    simp only [kk]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Finsupp.single_apply, Fin.castSucc_ne_last]
  · rfl

theorem vanish (LL : Letters N) (n : ℕ) (ρ : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hinv : IsFrozenInv p LL ρ n G) (h0 : ∀ m, kk ρ m = 0 → coeff m G = 0) : G = 0 := by
  classical
  by_contra hne
  have hex : ∃ k, ∃ m, kk ρ m = k ∧ coeff m G ≠ 0 := by
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hne
    exact ⟨_, m, rfl, hm⟩
  obtain ⟨m, hmk, hm⟩ := Nat.find_spec hex
  have hmin : ∀ ν, kk ρ ν < Nat.find hex → coeff ν G = 0 := fun ν hν => by
    by_contra h
    exact Nat.find_min hex hν ⟨ν, rfl, h⟩
  obtain ⟨c, hcρ, hc⟩ : ∃ c, c ≠ ρ ∧ m (Fin.last N, c) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hm
    apply h0
    simp only [kk]
    exact Finset.sum_eq_zero fun c' hc' => hcon c' (Finset.ne_of_mem_erase hc')
  set m' := m - Finsupp.single (Fin.last N, c) 1 + Finsupp.single (Fin.last N, ρ) 1 with hm'
  have hval : ∀ c', c' ≠ ρ → m' (Fin.last N, c') = m (Fin.last N, c') - (if c = c' then 1 else 0) := by
    intro c' hc'
    simp [hm', Finsupp.single_apply, Ne.symm hc']
  have hlt : kk ρ m' < kk ρ m := by
    simp only [kk]
    refine Finset.sum_lt_sum (fun c' hc' => ?_) ⟨c, Finset.mem_erase.2 ⟨hcρ, Finset.mem_univ _⟩, ?_⟩
    · rw [hval c' (Finset.ne_of_mem_erase hc')]
      exact Nat.sub_le _ _
    · rw [hval c hcρ, if_pos rfl]
      omega
  have hG' : ∀ ν, kk ρ ν = kk ρ m' → coeff ν G = 0 := fun ν hν => hmin ν (hν ▸ hmk ▸ hlt)
  have hc0 := congrArg (coeff m') (hinv c hcρ)
  simp only [glAct, LinearMap.sum_apply, MvPolynomial.coeff_sum, coeff_zero] at hc0
  rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (fun i _ => ?_), zero_add] at hc0
  · have hl : ((Fin.last N : Fin (N + 1)) : ℕ) < N + 1 := (Fin.last N).isLt
    rw [if_pos hl] at hc0
    simp only [snoc_vec_last, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, coeff_neg, neg_eq_zero] at hc0
    rw [MvPolynomial.coeff_X_mul', if_pos (by simp [hm'])] at hc0
    erw [MvPolynomial.coeff_pderiv] at hc0
    have e1 : m' - Finsupp.single (Fin.last N, ρ) 1 + Finsupp.single (Fin.last N, c) 1 = m := by
      rw [hm', add_tsub_cancel_right,
        tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hc))]
    have e2 : ((m' - Finsupp.single (Fin.last N, ρ) 1 : Fin (N + 1) × Fin r →₀ ℕ) (Fin.last N, c)) + 1 =
        m (Fin.last N, c) := by
      rw [hm', add_tsub_cancel_right, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    rw [e1] at hc0
    have e3 : ((((m' - Finsupp.single (Fin.last N, ρ) 1 : Fin (N + 1) × Fin r →₀ ℕ) (Fin.last N, c) : ℕ) :
        ℚ_[p]) + 1) = ((m (Fin.last N, c) : ℕ) : ℚ_[p]) := by exact_mod_cast e2
    rw [e3] at hc0
    rcases mul_eq_zero.1 hc0 with h | h
    · exact hm h
    · exact hc (by exact_mod_cast h)
  · have hci : ((Fin.castSucc i : Fin (N + 1)) : ℕ) < N + 1 := (Fin.castSucc i).isLt
    rw [if_pos hci]
    split_ifs
    · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact coeff_X_pderiv_castSucc ρ G m' hG' i c ρ
    · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, coeff_neg, neg_eq_zero]
      exact coeff_X_pderiv_castSucc ρ G m' hG' i ρ c

end Formalism.GM.M.FB

set_option linter.unusedSimpArgs false

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

lemma eq_ext_res (n : ℕ) (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hZ : ∀ c, c ≠ ρ → m (Fin.last N, c) = 0) (hrow : ∑ c, m (Fin.last N, c) = n) :
    m = ext n ρ (res m) := by
  ext ⟨i, c⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · by_cases hc : c = ρ
    · subst hc
      rw [ext_last, if_pos rfl, ← hrow, Finset.sum_eq_single c]
      · intro b _ hb
        exact hZ b hb
      · intro h
        exact absurd (Finset.mem_univ c) h
    · rw [ext_last, if_neg hc, hZ c hc]
  · rw [ext_castSucc, res_apply]

lemma mem_IntPol_iff {σ : Type} (x : MvPolynomial σ ℚ_[p]) :
    x ∈ IntPol p σ ↔ (x.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
  rw [← MvPolynomial.mem_range_map_iff_coeffs_subset]
  exact Iff.rfl

end Formalism.GM.M.FB

namespace Formalism.GM

open MvPolynomial Finset M.FB

theorem extendBijOn : M.FreezeBij := by
  intro p _ N r LL ρ n hS
  refine ⟨fun f _ g _ h => ?_, fun F hF hinv => ?_⟩
  · calc f = ev p ρ (M.freeze p LL ρ n f) := (ev_freeze LL ρ n f).symm
      _ = ev p ρ (M.freeze p LL ρ n g) := by rw [h]
      _ = g := ev_freeze LL ρ n g
  · obtain ⟨hFpol, hFint⟩ := Submodule.mem_inf.1 hF
    have hFsupp := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hFpol
    have hFn : ∀ m ∈ F.support, ∑ c, m (Fin.last N, c) = n := fun m hm => by
      have := (hFsupp (Finset.mem_coe.2 hm)) (Fin.last N)
      rwa [snoc_deg_last] at this
    obtain ⟨f, hf⟩ : ∃ f, f = ev p ρ F := ⟨_, rfl⟩
    have hcf : ∀ m', coeff m' f = coeff (ext n ρ m') F := fun m' => by rw [hf]; exact coeff_ev ρ n F hFn m'
    have hfpol : f ∈ M.Pol p r LL := by
      rw [M.Pol, MvPolynomial.mem_restrictSupport_iff]
      intro m' hm'
      have hne : coeff (ext n ρ m') F ≠ 0 := by
        rw [← hcf]
        exact MvPolynomial.mem_support_iff.1 hm'
      have hmd := hFsupp (Finset.mem_coe.2 (MvPolynomial.mem_support_iff.2 hne))
      intro i
      have := hmd (Fin.castSucc i)
      simpa [snoc_deg_castSucc, ext_castSucc] using this
    have hfint : f ∈ M.IntPol p (Fin N × Fin r) := by
      rw [mem_IntPol_iff] at hFint ⊢
      intro x hx
      obtain ⟨m', hm', rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hx
      rw [hcf]
      apply hFint
      exact MvPolynomial.coeff_mem_coeffs _ (by rw [← hcf]; exact MvPolynomial.mem_support_iff.1 hm')
    refine ⟨f, Submodule.mem_inf.2 ⟨hfpol, hfint⟩, ?_⟩
    have hfz : ∀ m ∈ (M.freeze p LL ρ n f).support, ∑ c, m (Fin.last N, c) = n := by
      intro m hm
      have := hom_freeze LL ρ n hS f hfpol (MvPolynomial.mem_support_iff.1 hm)
      rwa [weight_wL] at this
    have hG := vanish LL n ρ (M.freeze p LL ρ n f - F)
      (fun c hc => by rw [map_sub, freeze_inv LL ρ n f c hc, hinv c hc, sub_zero]) (fun m hkk => ?_)
    · exact sub_eq_zero.1 hG
    · rw [MvPolynomial.coeff_sub, sub_eq_zero]
      by_cases hrow : ∑ c, m (Fin.last N, c) = n
      · have hZ : ∀ c, c ≠ ρ → m (Fin.last N, c) = 0 := fun c hc => by
          simp only [kk] at hkk
          exact (Finset.sum_eq_zero_iff.1 hkk) c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ _⟩)
        rw [eq_ext_res n ρ m hZ hrow, ← coeff_ev ρ n _ hfz, ← coeff_ev ρ n F hFn, ev_freeze, hf]
      · have h1 : coeff m (M.freeze p LL ρ n f) = 0 := by
          by_contra h
          exact hrow (hfz m (MvPolynomial.mem_support_iff.2 h))
        have h2 : coeff m F = 0 := by
          by_contra h
          exact hrow (hFn m (MvPolynomial.mem_support_iff.2 h))
        rw [h1, h2]

end Formalism.GM
