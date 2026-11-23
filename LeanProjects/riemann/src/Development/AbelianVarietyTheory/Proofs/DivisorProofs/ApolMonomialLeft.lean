import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

noncomputable section

namespace GlobalTheory.HodgeDegPos

section General
variable {S : Type} [Fintype S] [DecidableEq S]

def facM (m : S →₀ ℕ) : ℝ := ∏ s, ((m s).factorial : ℝ)

omit [DecidableEq S] in
theorem facM_pos (m : S →₀ ℕ) : 0 < facM m :=
  Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _

theorem facM_sub (m : S →₀ ℕ) (s : S) (h : m s ≠ 0) :
    facM m = m s * facM (m - Finsupp.single s 1) := by
  unfold facM
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s), ← Finset.mul_prod_erase _ _ (Finset.mem_univ s),
    ← mul_assoc]
  congr 1
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
    simp [hk, Nat.factorial_succ]
  · refine Finset.prod_congr rfl fun t ht => ?_
    have := Finset.ne_of_mem_erase ht
    simp [Finsupp.single_apply, this.symm]

def apol (P : MvPolynomial S ℝ) : MvPolynomial S ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials S ℝ).constr ℝ fun m => facM m * P.coeff m

omit [DecidableEq S] in
theorem apol_monomial (P : MvPolynomial S ℝ) (m : S →₀ ℕ) (c : ℝ) :
    apol P (monomial m c) = c * (facM m * P.coeff m) := by
  have : (monomial m c : MvPolynomial S ℝ) = c • basisMonomials S ℝ m := by
    simp [coe_basisMonomials, smul_monomial]
  rw [this, map_smul, apol, Module.Basis.constr_basis, smul_eq_mul]

theorem apol_monomial_left (Q : MvPolynomial S ℝ) (m : S →₀ ℕ) (c : ℝ) :
    apol (monomial m c) Q = c * (facM m * Q.coeff m) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [apol_monomial, coeff_monomial, coeff_monomial]
    by_cases h : m = u
    · subst h; simp; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  | add p q hp hq => rw [map_add, hp, hq, coeff_add]; ring

theorem apol_lin (c : S → ℝ) (P Q : MvPolynomial S ℝ) :
    apol ((∑ s, C (c s) * X s) * P) Q = apol P (∑ s, c s • pderiv s Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [apol_monomial, map_sum, Finset.sum_mul, coeff_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, pderiv_monomial, apol_monomial, mul_assoc, coeff_C_mul, coeff_X_mul', smul_eq_mul]
    by_cases h : u s = 0
    · simp [h]
    · rw [if_pos (by simpa using h), facM_sub u s h]; ring
  | add p q hp hq =>
    simp only [map_add, smul_add, Finset.sum_add_distrib, hp, hq]

def dirD (c : S → ℝ) : Derivation ℝ (MvPolynomial S ℝ) (MvPolynomial S ℝ) := ∑ s, c s • pderiv s

theorem dirD_apply (c : S → ℝ) (Q : MvPolynomial S ℝ) : dirD c Q = ∑ s, c s • pderiv s Q := by
  unfold dirD
  induction (Finset.univ : Finset S) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]; rfl

theorem dirD_X (c : S → ℝ) (s : S) : dirD c (X s) = C (c s) := by
  rw [dirD_apply, Finset.sum_eq_single s]
  · simp [smul_eq_C_mul]
  · intro t _ ht; simp [pderiv_X_of_ne (Ne.symm ht)]
  · simp

theorem apol_pow (c : S → ℝ) (n : ℕ) (P Q : MvPolynomial S ℝ) :
    apol ((∑ s, C (c s) * X s) ^ n * P) Q = apol P ((dirD c)^[n] Q) := by
  induction n generalizing Q with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, apol_lin, ih, ← dirD_apply, Function.iterate_succ_apply]

end General

section Deriv
variable {A : Type} [CommRing A] [Algebra ℝ A] (D : Derivation ℝ A A)

theorem iter_mul (l F : A) (c : ℝ) (hl : D l = algebraMap ℝ A c) (n : ℕ) :
    D^[n + 1] (l * F) = l * D^[n + 1] F + (((n : ℝ) + 1) * c) • D^[n] F := by
  induction n with
  | zero => simp [hl, Algebra.smul_def]; ring
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add, Derivation.map_smul, Derivation.leibniz, hl,
      ← Function.iterate_succ_apply' D (n + 1), ← Function.iterate_succ_apply' D n]
    simp only [Algebra.smul_def, smul_eq_mul, map_mul, map_add, map_one, Nat.cast_add, Nat.cast_one, Algebra.algebraMap_self, RingHom.id_apply]
    ring

theorem iter_prod {κ : Type} (T : Finset κ) (l : κ → A) (W : A) (c : ℝ) (hW : D W = 0)
    (hl : ∀ p ∈ T, D (l p) = algebraMap ℝ A c) :
    D^[T.card] ((∏ p ∈ T, l p) * W) = ((T.card.factorial : ℝ) * c ^ T.card) • W := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih fun p hp => hl p (Finset.mem_insert_of_mem hp)
    rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha, mul_assoc,
      iter_mul D _ _ c (hl a (Finset.mem_insert_self _ _)), Function.iterate_succ_apply', ih',
      Derivation.map_smul, hW, smul_zero, mul_zero, zero_add, smul_smul, Nat.factorial_succ]
    congr 1
    push_cast
    ring

theorem deriv_prod_zero {κ : Type} (T : Finset κ) (l : κ → A) (hl : ∀ p ∈ T, D (l p) = 0) :
    D (∏ p ∈ T, l p) = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih fun p hp => hl p (Finset.mem_insert_of_mem hp),
      hl a (Finset.mem_insert_self _ _)]
    simp

end Deriv

theorem coeff_lead {S κ : Type} [Finite S] [LinearOrder S] (T : Finset κ) (u v : κ → S)
    (h : ∀ p ∈ T, u p < v p) :
    (∏ p ∈ T, (X (u p) - X (v p) : MvPolynomial S ℝ)).coeff (∑ p ∈ T, Finsupp.single (u p) 1) = 1 := by
  let m : MonomialOrder S := MonomialOrder.lex
  have hlt : ∀ p ∈ T, m.toSyn (m.degree (X (v p) : MvPolynomial S ℝ)) <
      m.toSyn (m.degree (X (u p) : MvPolynomial S ℝ)) := by
    intro p hp
    rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
    refine MonomialOrder.lex_lt_iff.mpr ?_
    exact Finsupp.Lex.single_strictAnti (h p hp)
  have hmon : ∀ p ∈ T, m.Monic (X (u p) - X (v p) : MvPolynomial S ℝ) := by
    intro p hp
    unfold MonomialOrder.Monic
    rw [MonomialOrder.leadingCoeff_sub_of_lt (hlt p hp), MonomialOrder.leadingCoeff_X]
  have h1 := (MonomialOrder.Monic.prod hmon).coeff_degree
  rw [MonomialOrder.degree_prod (fun p hp => (hmon p hp).ne_zero)] at h1
  rw [← h1]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [MonomialOrder.degree_sub_of_lt (hlt p hp), MonomialOrder.degree_X]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def rootP (p : ι × Fin N × Fin N) : Pol ι N := X (p.1, p.2.1) - X (p.1, p.2.2)

theorem alt_eq :
    (∑ σ : ι → Equiv.Perm (Fin N), monomial (permExp σ) (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) : Pol ι N) =
      ∏ p ∈ Finset.univ.filter (fun p : ι × Fin N × Fin N => p.2.1 < p.2.2), rootP p := by
  have h1 : ∀ τ : ι, (∏ a : Fin N, ∏ b : Fin N, if a < b then rootP (τ, a, b) else 1) =
      ∑ s : Equiv.Perm (Fin N), C ((Equiv.Perm.sign s : ℤ) : ℝ) *
        ∏ i : Fin N, (X (τ, i) : Pol ι N) ^ (N - 1 - (s i : ℕ)) := by
    intro τ
    have h := Matrix.det_projVandermonde (fun _ : Fin N => (1 : Pol ι N)) (fun i => X (τ, i))
    rw [← Matrix.det_transpose, Matrix.det_apply'] at h
    simp only [Matrix.transpose_apply, Matrix.projVandermonde_apply, one_pow, one_mul, Fin.val_rev] at h
    calc _ = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((X (τ, i) : Pol ι N) - X (τ, j)) := by
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [← Finset.prod_filter]
          refine Finset.prod_congr (by ext; simp) fun b _ => rfl
      _ = _ := by
          rw [← h]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_intCast]
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          congr 1
          omega
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [Fintype.prod_prod_type, h1]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type, map_prod]
  simp only [PPowSum.permExp_apply]

theorem facM_permExp (σ : ι → Equiv.Perm (Fin N)) :
    facM (permExp σ) = facM (permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))) := by
  unfold facM
  simp only [Fintype.prod_prod_type, PPowSum.permExp_apply]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact Equiv.prod_comp (σ τ) (fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ))

theorem degFl_eq_apol (P : Pol ι N) :
    facM (permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))) * degFl ι N P = (-1) ^ dimFl ι N *
      apol P (∏ p ∈ Finset.univ.filter (fun p : ι × Fin N × Fin N => p.2.1 < p.2.2), rootP p) := by
  rw [← alt_eq, map_sum, degFl, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [apol_monomial, facM_permExp σ]
  ring

def cf (j : ℕ) (x : ι × Fin N) : ℝ := if (x.2 : ℕ) < j then -1 else 1

omit [DecidableEq ι] in
theorem lamA_eq (j : ℕ) : lamA ι N j = ∑ x : ι × Fin N, C (cf j x) * X x := by
  unfold lamA pHigh pLow cf
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

def crossP (ι : Type) [Fintype ι] (N j : ℕ) : Finset (ι × Fin N × Fin N) :=
  Finset.univ.filter fun p => (p.2.1 : ℕ) < j ∧ j ≤ (p.2.2 : ℕ)

def sameP (ι : Type) [Fintype ι] (N j : ℕ) : Finset (ι × Fin N × Fin N) :=
  Finset.univ.filter fun p => p.2.1 < p.2.2 ∧ ¬ ((p.2.1 : ℕ) < j ∧ j ≤ (p.2.2 : ℕ))

theorem card_fin_filter (q : ℕ → Prop) [DecidablePred q] (a b : ℕ) (hb : b ≤ N) (h : ∀ i < N, q i ↔ a ≤ i ∧ i < b) :
    (Finset.univ.filter fun i : Fin N => q i).card = b - a := by
  rw [← Nat.card_Ico, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact (h k k.isLt).mp hk
  · intro hi; exact ⟨⟨i, by omega⟩, (h i (by omega)).mpr hi, rfl⟩

omit [DecidableEq ι] in
theorem card_crossP (j : ℕ) (hj : j ≤ N) : (crossP ι N j).card = dimGr ι N j := by
  have : crossP ι N j = Finset.univ ×ˢ ((Finset.univ.filter fun i : Fin N => (i : ℕ) < j) ×ˢ
      (Finset.univ.filter fun i : Fin N => j ≤ (i : ℕ))) := by
    ext p; simp [crossP]
  rw [this, Finset.card_product, Finset.card_product, card_fin_filter (fun i => i < j) 0 j hj (by omega),
    card_fin_filter (fun i => j ≤ i) j N le_rfl (by omega)]
  simp [dimGr]

omit [DecidableEq ι] in
theorem prod_split (j : ℕ) :
    ∏ p ∈ Finset.univ.filter (fun p : ι × Fin N × Fin N => p.2.1 < p.2.2), rootP p =
      (∏ p ∈ crossP ι N j, rootP p) * ∏ p ∈ sameP ι N j, rootP p := by
  rw [← Finset.prod_filter_mul_prod_filter_not _ (fun p : ι × Fin N × Fin N => (p.2.1 : ℕ) < j ∧ j ≤ (p.2.2 : ℕ)),
    Finset.filter_filter, Finset.filter_filter]
  congr 2
  ext p
  simp only [crossP, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  omega

def fibExp (ι : Type) [Fintype ι] (N j : ℕ) (x : ι × Fin N) : ℕ :=
  if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ)

theorem sum_sameP (j : ℕ) (hj : j ≤ N) :
    ∑ p ∈ sameP ι N j, Finsupp.single (p.1, p.2.1) 1 = Finsupp.equivFunOnFinite.symm (fibExp ι N j) := by
  ext ⟨τ, a⟩
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Finsupp.equivFunOnFinite_symm_apply_apply]
  rw [← Finset.card_filter]
  have : (sameP ι N j).filter (fun p => (p.1, p.2.1) = (τ, a)) =
      (Finset.univ.filter fun b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < j ∧ j ≤ (b : ℕ))).map
        ⟨fun b => (τ, a, b), fun b b' h => by simpa using h⟩ := by
    ext ⟨t, x, y⟩
    simp only [sameP, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, Finset.mem_map,
      Function.Embedding.coeFn_mk, Fin.lt_def]
    constructor
    · rintro ⟨h, rfl, rfl⟩; exact ⟨y, h, rfl⟩
    · rintro ⟨b, h, he⟩
      cases he
      exact ⟨h, rfl, rfl⟩
  rw [this, Finset.card_map]
  have ha := a.isLt
  simp only [fibExp]
  by_cases h : (a : ℕ) < j
  · rw [card_fin_filter (fun b => (a : ℕ) < b ∧ ¬ ((a : ℕ) < j ∧ j ≤ b)) (a + 1) j hj (by omega), if_pos h]
    omega
  · rw [card_fin_filter (fun b => (a : ℕ) < b ∧ ¬ ((a : ℕ) < j ∧ j ≤ b)) (a + 1) N le_rfl (by omega), if_neg h]
    omega

theorem coeff_sameP (j : ℕ) (hj : j ≤ N) :
    (∏ p ∈ sameP ι N j, rootP p).coeff (Finsupp.equivFunOnFinite.symm (fibExp ι N j)) = 1 := by
  rw [← sum_sameP j hj]
  let f : ι × Fin N → Fin (Fintype.card ι) ×ₗ Fin N := fun x => toLex (Fintype.equivFin ι x.1, x.2)
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simpa [f] using h
  refine @coeff_lead (ι × Fin N) _ _ (LinearOrder.lift' f hf) (sameP ι N j) (fun p => (p.1, p.2.1))
    (fun p => (p.1, p.2.2)) ?_
  intro p hp
  have : p.2.1 < p.2.2 := (Finset.mem_filter.mp hp).2.1
  change f _ < f _
  simp only [f, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨trivial, this⟩

omit [DecidableEq ι] in
theorem dim_add (j : ℕ) (hj : j ≤ N) : dimFl ι N = dimGr ι N j + ∑ x, fibExp ι N j x := by
  have h1 : ∑ i : Fin N, (if (i : ℕ) < j then N - j else 0) = j * (N - j) := by
    rw [← Finset.sum_filter, Finset.sum_const, card_fin_filter (fun i => i < j) 0 j hj (by omega)]
    simp
  rw [Fintype.sum_prod_type, dimFl, dimGr, ← PermutationPointDegree.sum_delta, ← h1]
  simp only [fibExp, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

theorem degFl_hodge_pow (j : ℕ) (hj : j ≤ N) :
    facM (permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))) * degFl ι N (lamA ι N j ^ dimGr ι N j * fibPt ι N j) =
      ((dimGr ι N j).factorial : ℝ) * 2 ^ dimGr ι N j * facM (Finsupp.equivFunOnFinite.symm (fibExp ι N j)) := by
  have hfib : fibPt ι N j = monomial (Finsupp.equivFunOnFinite.symm (fibExp ι N j))
      ((-1 : ℝ) ^ (∑ x, fibExp ι N j x)) := by
    have := PermutationPointDegree.prod_negX (fibExp ι N j)
    rw [C_mul_monomial, mul_one] at this
    exact this
  have hD : ∀ p : ι × Fin N × Fin N, dirD (cf j) (rootP p) = C (cf j (p.1, p.2.1) - cf j (p.1, p.2.2)) := by
    intro p; rw [rootP, map_sub, dirD_X, dirD_X, map_sub]
  have hit := iter_prod (dirD (cf (ι := ι) (N := N) j)) (crossP ι N j) rootP (∏ p ∈ sameP ι N j, rootP p) (-2)
    (deriv_prod_zero _ _ _ fun p hp => by
      have h := (Finset.mem_filter.mp hp).2
      rw [Fin.lt_def] at h
      rw [hD]
      unfold cf
      by_cases h1 : (p.2.1 : ℕ) < j
      · rw [if_pos h1, if_pos (show (p.2.2 : ℕ) < j by omega)]; simp
      · rw [if_neg h1, if_neg (show ¬ (p.2.2 : ℕ) < j by omega)]; simp)
    (fun p hp => by
      have h := (Finset.mem_filter.mp hp).2
      rw [hD]
      unfold cf
      rw [if_pos h.1, if_neg (show ¬ (p.2.2 : ℕ) < j by omega), algebraMap_eq]
      norm_num)
  rw [card_crossP j hj] at hit
  rw [degFl_eq_apol, lamA_eq, apol_pow, prod_split j, hit, map_smul, hfib, apol_monomial_left,
    coeff_sameP j hj, dim_add j hj, smul_eq_mul, pow_add, neg_pow (2 : ℝ)]
  have e1 : ∀ n : ℕ, ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := fun n => by rw [← mul_pow]; simp
  linear_combination (((dimGr ι N j).factorial : ℝ) * 2 ^ dimGr ι N j *
    facM (Finsupp.equivFunOnFinite.symm (fibExp ι N j))) *
      (((-1 : ℝ) ^ (∑ x, fibExp ι N j x)) ^ 2 * e1 (dimGr ι N j) + e1 (∑ x, fibExp ι N j x))

theorem degFl_lamA_pow_pos : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) [Nonempty ι] (j : ℕ), 1 ≤ j → j < N →
    0 < degFl ι N (lamA ι N j ^ dimGr ι N j * fibPt ι N j) := by
  intro ι _ _ N _ j _ hj
  refine (mul_pos_iff_of_pos_left (facM_pos (permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))))).mp ?_
  rw [degFl_hodge_pow j hj.le]
  have := facM_pos (Finsupp.equivFunOnFinite.symm (fibExp ι N j))
  positivity

end GlobalTheory.HodgeDegPos
