import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact

noncomputable section

open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm Formalism.DegreeFormula

namespace GlobalTheory.FlagFormDeg

section General

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def apolar (P : MvPolynomial V ℝ) : MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials V ℝ).constr ℝ fun m => (∏ x, ((m x).factorial : ℝ)) * P.coeff m

omit [DecidableEq V] in
theorem apolar_monomial (P : MvPolynomial V ℝ) (m : V →₀ ℕ) (c : ℝ) :
    apolar P (monomial m c) = c * ((∏ x, ((m x).factorial : ℝ)) * P.coeff m) := by
  have h : (monomial m c : MvPolynomial V ℝ) = c • basisMonomials V ℝ m := by
    simp [smul_monomial]
  rw [h, map_smul, apolar, Module.Basis.constr_basis, smul_eq_mul]

omit [Fintype V] in
theorem coeff_pderiv' (P : MvPolynomial V ℝ) (x : V) (m : V →₀ ℕ) :
    (pderiv x P).coeff m = ((m x : ℝ) + 1) * P.coeff (m + Finsupp.single x 1) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = m + Finsupp.single x 1
    · subst h
      simp [mul_comm]
    · rw [if_neg h, mul_zero]
      split_ifs with h2
      · by_cases hx : u x = 0
        · simp [hx]
        · exfalso
          apply h
          rw [← h2, tsub_add_cancel_of_le]
          rw [Finsupp.single_le_iff]
          omega
      · rfl
  | add p q hp hq => simp [hp, hq, mul_add]

theorem apolar_X_mul (P Q : MvPolynomial V ℝ) (x : V) :
    apolar P (X x * Q) = apolar (pderiv x P) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [X, monomial_mul, apolar_monomial, apolar_monomial, coeff_pderiv', one_mul, add_comm (Finsupp.single x 1) u]
    have : (∏ y, (((u + Finsupp.single x 1 : V →₀ ℕ) y).factorial : ℝ)) =
        (∏ y, ((u y).factorial : ℝ)) * ((u x : ℝ) + 1) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x), ← Finset.mul_prod_erase _ _ (Finset.mem_univ x)]
      have h2 : ∏ y ∈ Finset.univ.erase x, (((u + Finsupp.single x 1 : V →₀ ℕ) y).factorial : ℝ) =
          ∏ y ∈ Finset.univ.erase x, ((u y).factorial : ℝ) := by
        refine Finset.prod_congr rfl fun y hy => ?_
        have := Finset.ne_of_mem_erase hy
        simp [Finsupp.single_apply, this.symm]
      rw [h2]
      simp [Nat.factorial_succ]
      ring
    rw [this]
    ring
  | add p q hp hq => simp [hp, hq, mul_add]

omit [DecidableEq V] in
theorem apolar_sum_left {α : Type} (s : Finset α) (c : α → ℝ) (F : α → MvPolynomial V ℝ) (Q : MvPolynomial V ℝ) :
    apolar (∑ a ∈ s, C (c a) * F a) Q = ∑ a ∈ s, c a * apolar (F a) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    simp only [apolar_monomial, coeff_sum, coeff_C_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]

omit [Fintype E] in

theorem pderiv_aeval_lin (r : V → MvPolynomial E ℝ) (e : E) (c : V → ℝ) (h : ∀ x, pderiv e (r x) = C (c x))
    (P : MvPolynomial V ℝ) :
    pderiv e (aeval r P) = aeval r (∑ x, C (c x) * pderiv x P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p y hp =>
    have : ∑ x, C (c x) * pderiv x (p * X y) = (∑ x, C (c x) * pderiv x p) * X y + p * C (c y) := by
      simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, pderiv_X,
        Pi.single_apply]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => by ring
      · simp [mul_comm]
    rw [this, map_mul, Derivation.leibniz, hp, aeval_X, h, map_add, map_mul, map_mul, aeval_X, aeval_C]
    simp only [smul_eq_mul, algebraMap_eq]
    ring

theorem coeff_aeval_lin (r : V → MvPolynomial E ℝ) (c : E → V → ℝ) (h : ∀ e x, pderiv e (r x) = C (c e x))
    (h0 : ∀ x, constantCoeff (r x) = 0) (S : Finset E) (P : MvPolynomial V ℝ) :
    (aeval r P).coeff (∑ e ∈ S, Finsupp.single e 1) = apolar P (∏ e ∈ S, ∑ x, C (c e x) * X x) := by
  induction S using Finset.induction_on generalizing P with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty, ← C_1, C_apply, apolar_monomial]
    have : constantCoeff (aeval r P) = constantCoeff P := by
      induction P using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p y hp => simp [h0]
    simpa [constantCoeff_eq] using this
  | insert e S he ih =>
    have h1 := coeff_pderiv' (aeval r P) e (∑ e ∈ S, Finsupp.single e 1)
    have h2 : (∑ e ∈ S, Finsupp.single e 1 : E →₀ ℕ) e = 0 := by
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun f hf => ?_
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact he hf
    rw [h2, pderiv_aeval_lin r e (c e) (h e), ih, apolar_sum_left] at h1
    rw [Finset.sum_insert he, Finset.prod_insert he, add_comm, Finset.sum_mul, map_sum]
    simp only [Nat.cast_zero, zero_add, one_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, C_mul', map_smul, apolar_X_mul, smul_eq_mul]

end General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def inc (e : ι × Fin N × Fin N) (x : ι × Fin N) : ℝ :=
  if e.2.1 < e.2.2 then (if x = (e.1, e.2.2) then 1 else 0) - (if x = (e.1, e.2.1) then 1 else 0) else 0

omit [Fintype ι] in
theorem pderiv_rootForm (e : ι × Fin N × Fin N) (x : ι × Fin N) : pderiv e (rootForm x) = C (inc e x) := by
  obtain ⟨τ, a, b⟩ := e
  obtain ⟨s, i⟩ := x
  have h1 : ∑ a' : Fin N, pderiv (τ, a, b) (if a' < i then (X (s, a', i) : FormPol ι N) else 0) =
      if a < b then (if (s, i) = (τ, b) then 1 else 0) else 0 := by
    rw [Finset.sum_eq_single a]
    · by_cases h : (s, i) = (τ, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        by_cases h' : a < i <;> simp [h']
      · have : (s, a, i) ≠ (τ, a, b) := fun h' => h (by simp_all)
        by_cases h' : a < i <;> simp [h', h, pderiv_X_of_ne this]
    · intro a' _ ha
      have : (s, a', i) ≠ (τ, a, b) := fun h' => ha (by simp_all)
      by_cases h' : a' < i <;> simp [h', pderiv_X_of_ne this]
    · simp
  have h2 : ∑ b' : Fin N, pderiv (τ, a, b) (if i < b' then (X (s, i, b') : FormPol ι N) else 0) =
      if a < b then (if (s, i) = (τ, a) then 1 else 0) else 0 := by
    rw [Finset.sum_eq_single b]
    · by_cases h : (s, i) = (τ, a)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        by_cases h' : i < b <;> simp [h']
      · have : (s, i, b) ≠ (τ, a, b) := fun h' => h (by simp_all)
        by_cases h' : i < b <;> simp [h', h, pderiv_X_of_ne this]
    · intro b' _ hb
      have : (s, i, b') ≠ (τ, a, b) := fun h' => hb (by simp_all)
      by_cases h' : i < b' <;> simp [h', pderiv_X_of_ne this]
    · simp
  simp only [rootForm, map_sub, map_sum, inc]
  rw [h1, h2]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
theorem constantCoeff_rootForm (x : ι × Fin N) : constantCoeff (rootForm x) = 0 := by
  simp [rootForm, map_sum, apply_ite]

def pairs (ι : Type) [Fintype ι] (N : ℕ) : Finset (ι × Fin N × Fin N) := Finset.univ.filter fun e => e.2.1 < e.2.2

theorem volExp_eq : (volExp : (ι × Fin N × Fin N) →₀ ℕ) = ∑ e ∈ pairs ι N, Finsupp.single e 1 := by
  ext p
  simp [volExp, pairs, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem sum_card_Ioi (N : ℕ) : ∑ a : Fin N, (Finset.Ioi a).card = N * (N - 1) / 2 := by
  simp only [Fin.card_Ioi]
  rw [← Finset.sum_range_id, Fin.sum_univ_eq_sum_range (fun i => N - 1 - i), Finset.sum_range_reflect (fun i => i)]

omit [Fintype ι] [DecidableEq ι] in
theorem vandermonde_at (τ : ι) :
    (∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, b) - X (τ, a) : Pol ι N)) =
      (-1) ^ (N * (N - 1) / 2) * ∑ σ : Equiv.Perm (Fin N), C ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i : Fin N, X (τ, i) ^ (N - 1 - (σ i : ℕ)) := by
  have h := Matrix.det_projVandermonde (fun _ : Fin N => (1 : Pol ι N)) (fun i => X (τ, i))
  rw [← Matrix.det_transpose, Matrix.det_apply'] at h
  have h2 : ∑ σ : Equiv.Perm (Fin N), C ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i : Fin N, (X (τ, i) : Pol ι N) ^ (N - 1 - (σ i : ℕ)) =
      ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b) : Pol ι N) := by
    simp only [one_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Matrix.transpose_apply, Matrix.projVandermonde_apply, one_pow, one_mul, Fin.val_rev]
    congr 1
    omega
  rw [h2, ← sum_card_Ioi, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun b _ => by ring

theorem prod_pairs :
    (∏ e ∈ pairs ι N, ∑ x, C (inc e x) * X x : Pol ι N) =
      C ((-1) ^ dimFl ι N) * ∑ σ : ι → Equiv.Perm (Fin N),
        monomial (permExp σ) (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) := by
  have h1 : (∏ e ∈ pairs ι N, ∑ x, C (inc e x) * X x : Pol ι N) =
      ∏ τ : ι, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, b) - X (τ, a) : Pol ι N) := by
    rw [pairs, Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_filter]
    refine Finset.prod_congr (by ext; simp) fun b hb => ?_
    rw [Finset.mem_Ioi] at hb
    simp [inc, hb, sub_mul, Finset.sum_sub_distrib, apply_ite (C : ℝ → Pol ι N), ite_mul]
  rw [h1]
  simp only [vandermonde_at]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]
  congr 1
  · rw [dimFl, mul_comm, Finset.card_univ]
    simp
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    rfl

omit [DecidableEq ι] in
theorem factorial_permExp (σ : ι → Equiv.Perm (Fin N)) :
    ∏ x, ((permExp σ x).factorial : ℝ) = (superFact N : ℝ) ^ Fintype.card ι := by
  rw [Fintype.prod_prod_type, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have : ∏ i : Fin N, ((permExp σ (τ, i)).factorial : ℝ) = ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) :=
    Equiv.prod_comp (σ τ) fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ)
  rw [this, Fin.prod_univ_eq_prod_range (fun i => ((N - 1 - i).factorial : ℝ)),
    Finset.prod_range_reflect (fun i => (i.factorial : ℝ)), superFact, Nat.cast_prod]

theorem superFact_ne_zero (N : ℕ) : (superFact N : ℝ) ≠ 0 := by
  rw [superFact, Nat.cast_prod]
  exact Finset.prod_ne_zero_iff.2 fun k _ => Nat.cast_ne_zero.2 k.factorial_ne_zero

theorem degFl_eq_formDeg (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : Pol ι N) :
    degFl ι N P = formDeg (toForm P) := by
  rw [formDeg, toForm, volExp_eq, coeff_aeval_lin rootForm inc pderiv_rootForm constantCoeff_rootForm, prod_pairs,
    C_mul', map_smul, map_sum, eq_div_iff (pow_ne_zero _ (superFact_ne_zero N)), degFl, smul_eq_mul, mul_assoc,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [apolar_monomial, factorial_permExp]
  ring

end GlobalTheory.FlagFormDeg
