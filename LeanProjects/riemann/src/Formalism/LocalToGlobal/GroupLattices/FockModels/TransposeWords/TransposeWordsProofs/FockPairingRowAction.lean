import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

section general

variable {σ R : Type*} [CommRing R]

lemma tsact_eq_sum (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  refine Finset.sum_subset h fun m _ hm => ?_
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]

lemma tsact_symm (f g : MvPolynomial σ R) : fockR f g = fockR g f := by
  classical
  rw [tsact_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    tsact_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma tsact_add_left (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [tsact_eq_sum (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    tsact_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    tsact_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

lemma tsact_smul_left (c : R) (f g : MvPolynomial σ R) :
    fockR (c • f) g = c * fockR f g := by
  rw [tsact_eq_sum (c • f) g f.support MvPolynomial.support_smul]
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring

lemma tsact_zero_left (g : MvPolynomial σ R) : fockR (0 : MvPolynomial σ R) g = 0 := by
  unfold fockR
  simp

lemma tsact_sum_left {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ s, F i) g = ∑ i ∈ s, fockR (F i) g := by
  classical
  refine Finset.induction_on s (by simp [tsact_zero_left]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, tsact_add_left, ih]

lemma tsact_sum_right {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR g (∑ i ∈ s, F i) = ∑ i ∈ s, fockR g (F i) := by
  rw [tsact_symm, tsact_sum_left]
  exact Finset.sum_congr rfl fun i _ => tsact_symm _ _

lemma tsact_smul_right (c : R) (f g : MvPolynomial σ R) :
    fockR f (c • g) = c * fockR f g := by
  rw [tsact_symm, tsact_smul_left, tsact_symm]

lemma tsact_monomial_left (m : σ →₀ ℕ) (a : R) (h : MvPolynomial σ R) :
    fockR (monomial m a) h = a * h.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  classical
  by_cases ha : a = 0
  · subst ha; simp [tsact_zero_left]
  · unfold fockR
    rw [MvPolynomial.support_monomial, if_neg ha, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

lemma tsact_fact_eq (m : σ →₀ ℕ) (s : Finset σ) (h : m.support ⊆ s) :
    ∏ k ∈ m.support, (m k).factorial = ∏ k ∈ s, (m k).factorial := by
  refine Finset.prod_subset h fun k _ hk => ?_
  have h0 : m k = 0 := by simpa using hk
  rw [h0, Nat.factorial_zero]

lemma tsact_fact_succ (m : σ →₀ ℕ) (v : σ) :
    ∏ k ∈ (m + Finsupp.single v 1).support, ((m + Finsupp.single v 1 : σ →₀ ℕ) k).factorial
      = (m v + 1) * ∏ k ∈ m.support, (m k).factorial := by
  classical
  have h1 : (m + Finsupp.single v 1).support ⊆ insert v m.support := by
    intro k hk
    rw [Finset.mem_insert]
    by_cases hkv : k = v
    · exact Or.inl hkv
    · right
      simpa [Finsupp.mem_support_iff, Finsupp.single_apply, Ne.symm hkv] using hk
  rw [tsact_fact_eq _ _ h1, tsact_fact_eq m (insert v m.support) (Finset.subset_insert _ _),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v m.support),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v m.support)]
  have h2 : ∏ k ∈ (insert v m.support).erase v, ((m + Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ (insert v m.support).erase v, (m k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Finset.mem_erase] at hk
    simp [Finsupp.single_apply, Ne.symm hk.1]
  rw [h2]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

lemma tsact_X_mul (v : σ) (f h : MvPolynomial σ R) :
    fockR (f * X v) h = fockR f (pderiv v h) := by
  classical
  rw [tsact_eq_sum (f * X v) h _ (MvPolynomial.support_mul_X v f).le, Finset.sum_map]
  unfold fockR
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, MvPolynomial.coeff_pderiv, tsact_fact_succ]
  push_cast
  ring

end general

section what₂

variable {R : Type*} [CommRing R] {r n : ℕ}

lemma tsact_rowAct_X (G : Matrix (Fin r) (Fin r) R) (v : Fin r × Fin n) :
    rowAct R G (X v) = ∑ b : Fin r, C (G v.1 b) * X (b, v.2) := by
  simp [rowAct]

lemma tsact_coeff_zero (G : Matrix (Fin r) (Fin r) R) (h : MvPolynomial (Fin r × Fin n) R) :
    coeff 0 (rowAct R G h) = coeff 0 h := by
  show MvPolynomial.constantCoeff (rowAct R G h) = MvPolynomial.constantCoeff h
  induction h using MvPolynomial.induction_on
  next a => simp [rowAct]
  next p q hp hq => simp only [map_add, hp, hq]
  next p v hp => simp [hp, rowAct]

lemma tsact_chain (G : Matrix (Fin r) (Fin r) R) (b : Fin r) (s : Fin n) (h : MvPolynomial (Fin r × Fin n) R) :
    pderiv (b, s) (rowAct R G h) = ∑ a : Fin r, G a b • rowAct R G (pderiv (a, s) h) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    obtain ⟨c, t⟩ := v
    have hL : pderiv (b, s) (∑ d : Fin r, C (G c d) * X (d, t) : MvPolynomial (Fin r × Fin n) R)
        = if t = s then C (G c b) else 0 := by
      rw [map_sum]
      simp only [pderiv_C_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [eq_comm]
      · simp [hts]
    have hR : ∑ a : Fin r, G a b • (rowAct R G p * rowAct R G (pderiv (a, s) (X (c, t))))
        = rowAct R G p * (if t = s then C (G c b) else 0) := by
      simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [apply_ite, Finset.sum_ite_eq, smul_eq_C_mul, mul_comm]
      · simp [hts]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, tsact_rowAct_X, hL, hp]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [hR]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm]

end what₂

theorem fock_pairing_row_action : FockRRowAct := by
  intro R _ r n g P
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro Q
    have h1 : rowAct R g (C a : MvPolynomial (Fin r × Fin n) R) = C a := by simp [rowAct]
    rw [h1, C_apply, tsact_monomial_left, tsact_monomial_left, tsact_coeff_zero]
  | add p q hp hq =>
    intro Q
    rw [map_add, tsact_add_left, tsact_add_left, hp, hq]
  | mul_X p v hp =>
    intro Q
    rw [map_mul, tsact_rowAct_X, Finset.mul_sum, tsact_sum_left, tsact_X_mul, tsact_chain, tsact_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : rowAct R g p * (C (g v.1 b) * X (b, v.2)) = g v.1 b • (rowAct R g p * X (b, v.2)) := by
      rw [smul_eq_C_mul]; ring
    rw [e, tsact_smul_left, tsact_X_mul, hp, tsact_smul_right, Matrix.transpose_apply]

end Formalism.L2.G.Model.TS
