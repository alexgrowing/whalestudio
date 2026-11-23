import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RenameSwapAtMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.SwapDefect

open GlobalTheory.FlagFormDeg GlobalTheory.BlockPoint GlobalTheory.FlagAnti

section General

variable {V : Type} [Fintype V] [DecidableEq V]

private theorem apolar_symm (P Q : MvPolynomial V ℝ) : apolar P Q = apolar Q P := by
  induction Q using MvPolynomial.induction_on' generalizing P with
  | monomial u a =>
    induction P using MvPolynomial.induction_on' with
    | monomial v b =>
      rw [apolar_monomial, apolar_monomial, coeff_monomial, coeff_monomial]
      by_cases h : u = v
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    | add p q hp hq =>
      rw [map_add, ← hp, ← hq, apolar_monomial, apolar_monomial, apolar_monomial, coeff_add]; ring
  | add p q hp hq =>
    have h := apolar_sum_left (Finset.univ : Finset Bool) (fun _ => 1) (fun t => if t then p else q) P
    simp at h
    rw [map_add, hp, hq, h]

private theorem apolar_rename (f : V → V) (hf : Function.Involutive f) (P Q : MvPolynomial V ℝ) :
    apolar (rename f P) (rename f Q) = apolar P Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [rename_monomial, apolar_monomial, apolar_monomial, coeff_rename_mapDomain f hf.injective]
    congr 2
    rw [← Equiv.prod_comp hf.toPerm]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Function.Involutive.coe_toPerm, Finsupp.mapDomain_apply hf.injective]
  | add p q hp hq => simp only [map_add, hp, hq]

private theorem apolar_rename' (f : V → V) (hf : Function.Involutive f) (P Q : MvPolynomial V ℝ) :
    apolar P (rename f Q) = apolar (rename f P) Q := by
  rw [← apolar_rename f hf (rename f P) Q, rename_rename, hf.comp_self, rename_id]
  rfl

omit [Fintype V] in
private theorem pderiv_mid {x y : V} (hxy : x ≠ y) (M : MvPolynomial V ℝ) :
    pderiv y (mid x y M) = pderiv x (mid x y M) := by
  induction M using MvPolynomial.induction_on with
  | C a => simp [mid]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p z hp =>
    have : pderiv y (mid x y (X z)) = pderiv x (mid x y (X z)) := by
      by_cases hx : z = x
      · subst hx; rw [mid_X_left]; simp [pderiv_X_of_ne hxy, pderiv_X_of_ne hxy.symm]
      by_cases hy : z = y
      · subst hy; rw [mid_X_right]; simp [pderiv_X_of_ne hxy, pderiv_X_of_ne hxy.symm]
      · rw [mid_X_of_ne hx hy, pderiv_X_of_ne hx, pderiv_X_of_ne hy]
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, this]

omit [Fintype V] [DecidableEq V] in
private theorem eq_zero_of_mid (x y : V) (L : MvPolynomial V ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ (j : ℕ) (M : MvPolynomial V ℝ), L ((X y - X x) ^ j * mid x y M) = 0) (Q : MvPolynomial V ℝ) :
    L Q = 0 := by
  suffices h : ∀ (j : ℕ) (M : MvPolynomial V ℝ), L ((X y - X x) ^ j * mid x y M * Q) = 0 by
    simpa using h 0 1
  have h2 : (C (1 / 2) : MvPolynomial V ℝ) * 2 = 1 := by
    rw [← map_ofNat (C : ℝ →+* MvPolynomial V ℝ) 2, ← map_mul]; norm_num
  induction Q using MvPolynomial.induction_on with
  | C a =>
    intro j M
    rw [mul_comm _ (C a), C_mul', map_smul, hL, smul_zero]
  | add p q hp hq => intro j M; rw [mul_add, map_add, hp, hq, add_zero]
  | mul_X p z hp =>
    intro j M
    by_cases hx : z = x
    · subst hx
      have : (X y - X z) ^ j * mid z y M * (p * X z) = (X y - X z) ^ j * mid z y (M * X z) * p
          - C (1 / 2) * ((X y - X z) ^ (j + 1) * mid z y M * p) := by
        rw [map_mul, mid_X_left]
        linear_combination (-((X y - X z) ^ j * mid z y M * p * X z)) * h2
      rw [this, map_sub, C_mul', map_smul, hp, hp]; simp
    by_cases hy : z = y
    · subst hy
      have : (X z - X x) ^ j * mid x z M * (p * X z) = (X z - X x) ^ j * mid x z (M * X z) * p
          + C (1 / 2) * ((X z - X x) ^ (j + 1) * mid x z M * p) := by
        rw [map_mul, mid_X_right]
        linear_combination (-((X z - X x) ^ j * mid x z M * p * X z)) * h2
      rw [this, map_add, C_mul', map_smul, hp, hp]; simp
    · have : (X y - X x) ^ j * mid x y M * (p * X z) = (X y - X x) ^ j * mid x y (M * X z) * p := by
        rw [map_mul, mid_X_of_ne hx hy]; ring
      rw [this, hp]

private theorem apolar_u_mul {x y : V} (hxy : x ≠ y) (W M : MvPolynomial V ℝ) (j : ℕ) :
    apolar ((X y - X x) * W) ((X y - X x) ^ (j + 1) * mid x y M) =
      2 * ((j : ℝ) + 1) * apolar W ((X y - X x) ^ j * mid x y M) := by
  rw [apolar_symm, sub_mul (X y), map_sub, apolar_X_mul, apolar_X_mul, apolar_symm, apolar_symm _ W, ← map_sub,
    ← smul_eq_mul (2 * ((j : ℝ) + 1)), ← map_smul]
  congr 1
  rw [Derivation.leibniz, Derivation.leibniz, pderiv_mid hxy, Derivation.leibniz_pow, Derivation.leibniz_pow,
    ← C_mul']
  simp only [map_sub, pderiv_X_self, pderiv_X_of_ne hxy, pderiv_X_of_ne hxy.symm, smul_eq_mul, nsmul_eq_mul,
    map_mul, map_add, map_natCast, map_one, map_ofNat, Nat.add_sub_cancel]
  push_cast
  ring

end General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

private def rt (e : ι × Fin N × Fin N) : Pol ι N := X (e.1, e.2.2) - X (e.1, e.2.1)

private theorem sum_inc {e : ι × Fin N × Fin N} (he : e ∈ pairs ι N) : (∑ x, C (inc e x) * X x : Pol ι N) = rt e := by
  have hb : e.2.1 < e.2.2 := (Finset.mem_filter.1 he).2
  simp [inc, hb, rt, sub_mul, Finset.sum_sub_distrib, apply_ite (C : ℝ → Pol ι N), ite_mul]

private theorem deg_eq (P : Pol ι N) :
    degFl ι N P = apolar (∏ e ∈ pairs ι N, rt e) P / (superFact N : ℝ) ^ Fintype.card ι := by
  rw [degFl_eq_formDeg, formDeg, toForm, volExp_eq,
    coeff_aeval_lin rootForm inc pderiv_rootForm constantCoeff_rootForm, apolar_symm,
    Finset.prod_congr rfl fun e he => sum_inc he]

private theorem bc_eq (τ : ι) (Q : Pol ι N) :
    formDeg (bcForm τ * toForm Q) =
      apolar Q (∑ e ∈ pairs ι N, if e.1 = τ then ∏ e' ∈ (pairs ι N).erase e, rt e' else 0) /
        (superFact N : ℝ) ^ Fintype.card ι := by
  have h : (bcForm τ : FormPol ι N) = ∑ e ∈ pairs ι N, if e.1 = τ then X e else 0 := by
    rw [pairs, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single τ, Fintype.sum_prod_type, bcForm]
    · simp
    · intro s _ hs; simp [hs]
    · simp
  rw [formDeg, h, Finset.sum_mul, coeff_sum, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  split_ifs
  · rw [volExp_eq, ← Finset.add_sum_erase _ _ he, coeff_X_mul, toForm,
      coeff_aeval_lin rootForm inc pderiv_rootForm constantCoeff_rootForm,
      Finset.prod_congr rfl fun e he => sum_inc (Finset.mem_of_mem_erase he)]
  · simp

private def sw (σ : ι) (a b : Fin N) (e : ι × Fin N × Fin N) : ι × Fin N × Fin N :=
  if e.1 = σ then (e.1, Equiv.swap a b e.2.1, Equiv.swap a b e.2.2) else e

omit [Fintype ι] in
private theorem sw_invol (σ : ι) (a b : Fin N) : Function.Involutive (sw σ a b) := fun e => by
  by_cases h : e.1 = σ
  · obtain ⟨t, c, d⟩ := e
    simp only at h
    simp [sw, h]
  · simp [sw, h]

omit [Fintype ι] in
private theorem sw_fst (σ : ι) (a b : Fin N) (e : ι × Fin N × Fin N) : (sw σ a b e).1 = e.1 := by
  unfold sw; split_ifs <;> rfl

omit [Fintype ι] in
private theorem rename_rt (σ : ι) (a b : Fin N) (e : ι × Fin N × Fin N) :
    rename (swapAt σ a b) (rt e) = rt (sw σ a b e) := by
  by_cases h : e.1 = σ <;> simp [rt, sw, swapAt, h]

private theorem sw_mem {σ : ι} {a b : Fin N} (hab : (b : ℕ) = a + 1) {e : ι × Fin N × Fin N}
    (he : e ∈ (pairs ι N).erase (σ, a, b)) : sw σ a b e ∈ (pairs ι N).erase (σ, a, b) := by
  obtain ⟨t, c, d⟩ := e
  by_cases h : t = σ
  · subst h
    simp only [sw, if_true, pairs, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
      Prod.mk.injEq, Equiv.swap_apply_def, Fin.lt_def, Fin.ext_iff] at he ⊢
    split_ifs <;> omega
  · simpa [sw, h] using he

private theorem rename_prod {σ : ι} {a b : Fin N} (hab : (b : ℕ) = a + 1) :
    rename (swapAt σ a b) (∏ e ∈ (pairs ι N).erase (σ, a, b), rt e) = ∏ e ∈ (pairs ι N).erase (σ, a, b), rt e := by
  rw [map_prod]
  exact Finset.prod_bij' (fun e _ => sw σ a b e) (fun e _ => sw σ a b e) (fun e he => sw_mem hab he)
    (fun e he => sw_mem hab he) (fun e _ => sw_invol σ a b e) (fun e _ => sw_invol σ a b e)
    (fun e _ => rename_rt σ a b e)

private theorem rename_sum (τ : ι) {σ : ι} {a b : Fin N} (hab : (b : ℕ) = a + 1) :
    rename (swapAt σ a b) (∑ e ∈ (pairs ι N).erase (σ, a, b),
        if e.1 = τ then ∏ e' ∈ ((pairs ι N).erase (σ, a, b)).erase e, rt e' else 0) =
      ∑ e ∈ (pairs ι N).erase (σ, a, b),
        if e.1 = τ then ∏ e' ∈ ((pairs ι N).erase (σ, a, b)).erase e, rt e' else 0 := by
  rw [map_sum]
  refine Finset.sum_bij' (fun e _ => sw σ a b e) (fun e _ => sw σ a b e) (fun e he => sw_mem hab he)
    (fun e he => sw_mem hab he) (fun e _ => sw_invol σ a b e) (fun e _ => sw_invol σ a b e)
    (fun e _ => ?_)
  rw [sw_fst]
  split_ifs
  · rw [map_prod]
    refine Finset.prod_bij' (fun e _ => sw σ a b e) (fun e _ => sw σ a b e) (fun f hf => ?_)
      (fun f hf => ?_) (fun e _ => sw_invol σ a b e) (fun e _ => sw_invol σ a b e)
      (fun e _ => rename_rt σ a b e)
    · exact Finset.mem_erase.2 ⟨(sw_invol σ a b).injective.ne (Finset.ne_of_mem_erase hf),
        sw_mem hab (Finset.mem_of_mem_erase hf)⟩
    · refine Finset.mem_erase.2 ⟨fun h => Finset.ne_of_mem_erase hf ?_, sw_mem hab (Finset.mem_of_mem_erase hf)⟩
      rw [← h, sw_invol]
  · simp

private theorem mem_pairs (σ : ι) {a b : Fin N} (hab : (b : ℕ) = a + 1) : (σ, a, b) ∈ pairs ι N := by
  simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]; omega

omit [Fintype ι] in
private theorem rename_u (σ : ι) (a b : Fin N) :
    rename (swapAt σ a b) (X (σ, b) - X (σ, a) : Pol ι N) = -(X (σ, b) - X (σ, a)) := by
  simp [swapAt]

private theorem vol_eq (σ : ι) {a b : Fin N} (hab : (b : ℕ) = a + 1) :
    ∏ e ∈ pairs ι N, rt e = (X (σ, b) - X (σ, a)) * ∏ e ∈ (pairs ι N).erase (σ, a, b), rt e :=
  (Finset.mul_prod_erase _ _ (mem_pairs σ hab)).symm

omit [Fintype ι] in
private theorem rename_pSum (τ σ : ι) (a b : Fin N) (k : ℕ) :
    rename (swapAt σ a b) (pSum τ k : Pol ι N) = pSum τ k := by
  by_cases h : τ = σ
  · subst h
    simp only [pSum, map_sum, map_pow, rename_X, swapAt, if_true]
    exact Equiv.sum_comp (Equiv.swap a b) fun i => (X (τ, i) : Pol ι N) ^ k
  · simp [pSum, swapAt, h]

private theorem deg_rename (σ : ι) {a b : Fin N} (hab : (b : ℕ) = a + 1) (P : Pol ι N) :
    degFl ι N (rename (swapAt σ a b) P) = -degFl ι N P := by
  rw [deg_eq, deg_eq, apolar_rename' _ (swapAt_swapAt σ a b), vol_eq σ hab, map_mul, rename_prod hab, rename_u,
    neg_mul, apolar_symm, map_neg, apolar_symm, neg_div]

private theorem apolar_pSum (τ : ι) (G : Pol ι N) : apolar (∏ e ∈ pairs ι N, rt e) (pSum τ 2 * G) = 0 := by
  have hc : (superFact N : ℝ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (superFact_ne_zero N)
  let L : Pol ι N →ₗ[ℝ] ℝ := (apolar (∏ e ∈ pairs ι N, rt e)).comp (LinearMap.mulLeft ℝ (pSum τ 2))
  have hL (P : Pol ι N) : L P = degFl ι N (pSum τ 2 * P) * (superFact N : ℝ) ^ Fintype.card ι := by
    rw [deg_eq, div_mul_cancel₀ _ hc]; rfl
  show L G = 0
  rw [← sum_homogeneousComponent G, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := homogeneousComponent_isHomogeneous k G
  by_cases e : k < dimFl ι N
  · refine eq_zero_of_anti L (fun σ a b hab P _ => ?_) e hk
    rw [hL, hL, ← neg_mul, ← deg_rename σ hab, map_mul, rename_pSum]
  · rw [hL, degFl_eq_formDeg,
      formDeg_eq_zero (isHomogeneous_toForm ((isHomogeneous_pSum_two τ).mul hk)) (by omega), zero_mul]

omit [Fintype ι] in
private theorem rename_mid (σ : ι) (a b : Fin N) (M : Pol ι N) :
    rename (swapAt σ a b) (mid (σ, a) (σ, b) M) = mid (σ, a) (σ, b) M := by
  induction M using MvPolynomial.induction_on with
  | C c => simp [mid]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p z hp =>
    rw [map_mul, map_mul, hp]
    congr 1
    by_cases hx : z = (σ, a)
    · subst hx; rw [mid_X_left]; simp [swapAt, add_comm]
    by_cases hy : z = (σ, b)
    · subst hy; rw [mid_X_right]; simp [swapAt, add_comm]
    · rw [mid_X_of_ne hx hy, rename_X]
      obtain ⟨t, i⟩ := z
      by_cases h : t = σ
      · subst h
        simp only [Prod.mk.injEq, true_and] at hx hy
        simp [swapAt, Equiv.swap_apply_of_ne_of_ne hx hy]
      · simp [swapAt, h]

omit [Fintype ι] in
private theorem pSum_eq (τ σ : ι) {a b : Fin N} (hab : a ≠ b) :
    (pSum τ 2 : Pol ι N) = mid (σ, a) (σ, b) (pSum τ 2) +
      C (if σ = τ then 1 / 2 else 0) * (X (σ, b) - X (σ, a)) ^ 2 := by
  rw [← sub_eq_iff_eq_add', pSum, map_sum, ← Finset.sum_sub_distrib]
  split_ifs with h
  · subst h
    have h2 : (C (1 / 2) : Pol ι N) * 2 = 1 := by
      rw [← map_ofNat (C : ℝ →+* Pol ι N) 2, ← map_mul]; norm_num
    rw [Fintype.sum_eq_add a b hab, map_pow, map_pow, mid_X_left, mid_X_right]
    · linear_combination (-(X (σ, a) ^ 2 + X (σ, b) ^ 2) - C (1 / 2) * (X (σ, a) + X (σ, b)) ^ 2) * h2
    · intro c hc
      rw [map_pow, mid_X_of_ne (by simp [hc.1]) (by simp [hc.2]), sub_self]
  · rw [C_0, zero_mul]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [map_pow, mid_X_of_ne (by simp [Ne.symm h]) (by simp [Ne.symm h]), sub_self]

private theorem bc_sum (τ σ : ι) {a b : Fin N} (hab : (b : ℕ) = a + 1) (Q : Pol ι N) :
    formDeg (bcForm τ * toForm (rename (swapAt σ a b) Q)) + formDeg (bcForm τ * toForm Q) =
      4 * (if σ = τ then 1 / 2 else 0) * apolar (∏ e ∈ (pairs ι N).erase (σ, a, b), rt e) Q /
        (superFact N : ℝ) ^ Fintype.card ι := by
  have hB : (∑ e ∈ pairs ι N, if e.1 = τ then ∏ e' ∈ (pairs ι N).erase e, rt e' else 0) =
      (if σ = τ then ∏ e ∈ (pairs ι N).erase (σ, a, b), rt e else 0) + (X (σ, b) - X (σ, a)) *
        ∑ e ∈ (pairs ι N).erase (σ, a, b),
          if e.1 = τ then ∏ e' ∈ ((pairs ι N).erase (σ, a, b)).erase e, rt e' else 0 := by
    rw [← Finset.add_sum_erase _ _ (mem_pairs σ hab), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    split_ifs
    · rw [Finset.erase_right_comm]
      exact (Finset.mul_prod_erase _ _
        (Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase he).symm, mem_pairs σ hab⟩)).symm
    · simp
  rw [bc_eq, bc_eq, ← apolar_rename' _ (swapAt_swapAt σ a b), ← add_div, ← map_add, hB, map_add (rename _), map_mul,
    rename_sum τ hab, rename_u, apolar_symm (∏ e ∈ (pairs ι N).erase (σ, a, b), rt e) Q]
  congr 1
  rw [← smul_eq_mul (4 * _ : ℝ), ← map_smul]
  congr 1
  split_ifs
  · rw [rename_prod hab]
    norm_num
    rw [two_smul]
    ring
  · rw [map_zero, mul_zero, zero_smul]
    ring

private theorem main (hh : Pol ι N →ₗ[ℝ] ℝ) (τ σ : ι) {a b : Fin N} (hab : (b : ℕ) = a + 1)
    (H : ∀ (k : ℕ) (M : Pol ι N), hh ((X (σ, b) - X (σ, a)) ^ (2 * k) * mid (σ, a) (σ, b) M) =
      oddHarm k * degFl ι N ((X (σ, b) - X (σ, a)) ^ (2 * k - 1) * mid (σ, a) (σ, b) M)) (Q : Pol ι N) :
    hh (pSum τ 2 * rename (swapAt σ a b) Q) + hh (pSum τ 2 * Q) =
      4 * (if σ = τ then 1 / 2 else 0) * apolar (∏ e ∈ (pairs ι N).erase (σ, a, b), rt e) Q /
        (superFact N : ℝ) ^ Fintype.card ι := by
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hxy : (σ, a) ≠ (σ, b) := fun h => hne (Prod.mk.inj h).2
  have hp := pSum_eq τ σ hne
  set ε : ℝ := if σ = τ then 1 / 2 else 0
  set c : ℝ := (superFact N : ℝ) ^ Fintype.card ι with hc
  set W : Pol ι N := ∏ e ∈ (pairs ι N).erase (σ, a, b), rt e with hW
  let A : Pol ι N →ₗ[ℝ] ℝ := hh.comp (LinearMap.mulLeft ℝ (pSum τ 2))
  let L : Pol ι N →ₗ[ℝ] ℝ := A.comp (rename (swapAt σ a b)).toLinearMap + A - (4 * ε / c) • apolar W
  have hL (P : Pol ι N) : L P = hh (pSum τ 2 * rename (swapAt σ a b) P) + hh (pSum τ 2 * P) -
      4 * ε * apolar W P / c := by
    show _ + _ - (4 * ε / c) * _ = _
    congr 1
    ring
  rw [← sub_eq_zero, ← hL]
  refine eq_zero_of_mid (σ, a) (σ, b) L (fun j M => ?_) Q
  rw [hL]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · have hs : rename (swapAt σ a b) ((X (σ, b) - X (σ, a)) ^ (2 * k) * mid (σ, a) (σ, b) M) =
        (X (σ, b) - X (σ, a)) ^ (2 * k) * mid (σ, a) (σ, b) M := by
      rw [map_mul, map_pow, rename_u, rename_mid, Even.neg_pow (even_two_mul k)]
    have h1 : pSum τ 2 * ((X (σ, b) - X (σ, a)) ^ (2 * k) * mid (σ, a) (σ, b) M) =
        (X (σ, b) - X (σ, a)) ^ (2 * k) * mid (σ, a) (σ, b) (pSum τ 2 * M) +
          C ε * ((X (σ, b) - X (σ, a)) ^ (2 * (k + 1)) * mid (σ, a) (σ, b) M) := by
      rw [map_mul]
      linear_combination ((X (σ, b) - X (σ, a)) ^ (2 * k) * mid (σ, a) (σ, b) M) * hp
    have h2 : degFl ι N ((X (σ, b) - X (σ, a)) ^ (2 * k + 1) * mid (σ, a) (σ, b) M) =
        2 * (2 * (k : ℝ) + 1) * apolar W ((X (σ, b) - X (σ, a)) ^ (2 * k) * mid (σ, a) (σ, b) M) / c := by
      rw [deg_eq, vol_eq σ hab, apolar_u_mul hxy]
      push_cast
      rfl
    have h3 : oddHarm k * degFl ι N ((X (σ, b) - X (σ, a)) ^ (2 * k - 1) * mid (σ, a) (σ, b) (pSum τ 2 * M)) =
        -(oddHarm k * ε * degFl ι N ((X (σ, b) - X (σ, a)) ^ (2 * k + 1) * mid (σ, a) (σ, b) M)) := by
      rcases k with _ | k
      · simp
      have h4 : (X (σ, b) - X (σ, a)) ^ (2 * (k + 1) - 1) * mid (σ, a) (σ, b) (pSum τ 2 * M) =
          pSum τ 2 * ((X (σ, b) - X (σ, a)) ^ (2 * k + 1) * mid (σ, a) (σ, b) M) -
            C ε * ((X (σ, b) - X (σ, a)) ^ (2 * (k + 1) + 1) * mid (σ, a) (σ, b) M) := by
        rw [map_mul, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
        linear_combination (-((X (σ, b) - X (σ, a)) ^ (2 * k + 1) * mid (σ, a) (σ, b) M)) * hp
      rw [h4, deg_eq, deg_eq, map_sub, apolar_pSum, C_mul', map_smul, smul_eq_mul]
      ring
    rw [hs, h1, map_add, C_mul', map_smul, H, H, h3, show 2 * (k + 1) - 1 = 2 * k + 1 by omega, h2, oddHarm_succ,
      smul_eq_mul]
    have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · have hs : rename (swapAt σ a b) ((X (σ, b) - X (σ, a)) ^ (2 * k + 1) * mid (σ, a) (σ, b) M) =
        -((X (σ, b) - X (σ, a)) ^ (2 * k + 1) * mid (σ, a) (σ, b) M) := by
      rw [map_mul, map_pow, rename_u, rename_mid, Odd.neg_pow (odd_two_mul_add_one k), neg_mul]
    have h1 := apolar_rename' _ (swapAt_swapAt σ a b) W ((X (σ, b) - X (σ, a)) ^ (2 * k + 1) * mid (σ, a) (σ, b) M)
    rw [hs, map_neg, hW, rename_prod hab, ← hW] at h1
    have h2 : apolar W ((X (σ, b) - X (σ, a)) ^ (2 * k + 1) * mid (σ, a) (σ, b) M) = 0 := by linarith
    rw [hs, mul_neg, map_neg, h2]
    ring

end GlobalTheory.SwapDefect

theorem _root_.GlobalTheory.T.block_point_harmonic_degree_flag : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (hh : Pol ι N →ₗ[ℝ] ℝ), (∀ (P : Pol ι N) (d : ℕ), d ≠ dimFl ι N + 1 → P.IsHomogeneous d → hh P = 0) → ∀ (τ σ : ι) (a b : Fin N), (b : ℕ) = a + 1 → (∀ (k : ℕ) (M : Pol ι N), hh ((X (σ, b) - X (σ, a)) ^ (2 * k) * GlobalTheory.BlockPoint.mid (σ, a) (σ, b) M) = GlobalTheory.BlockPoint.oddHarm k * degFl ι N ((X (σ, b) - X (σ, a)) ^ (2 * k - 1) * GlobalTheory.BlockPoint.mid (σ, a) (σ, b) M)) → ∀ Q : Pol ι N, Q.IsHomogeneous (dimFl ι N - 1) → hh (pSum τ 2 * rename (swapAt σ a b) Q) - formDeg (bcForm τ * toForm (rename (swapAt σ a b) Q)) = -(hh (pSum τ 2 * Q) - formDeg (bcForm τ * toForm Q)) := by
  intro ι _ _ N hh _ τ σ a b hab H Q _
  have h1 := GlobalTheory.SwapDefect.main hh τ σ hab H Q
  have h2 := GlobalTheory.SwapDefect.bc_sum τ σ hab Q
  linarith

end
