import Formalism.RealPlaceAnalysis.StatementE

open Finset

noncomputable section

namespace Formalism.REAL

lemma shiftedGenerator_eq_ite_smul_add {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ)
    (a b : Fin n) : Tm E x a b = (if a = b then x else 0) • (1 : A) + E a b := by
  unfold Tm
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]

lemma ite_zero_eq_mul_ite (P : Prop) [Decidable P] (x : ℂ) :
    (if P then x else 0) = x * (if P then 1 else 0) := by
  split_ifs <;> simp

lemma ite_zero_eq_ite_smul {A : Type*} [Ring A] [Algebra ℂ A] (P : Prop) [Decidable P] (X : A) :
    (if P then X else 0) = (if P then (1 : ℂ) else 0) • X := by
  split_ifs <;> simp

private theorem Tm_eq_smul_one_add {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (x : ℂ) (a b : Fin n) :
    Tm E x a b = (x * (if a = b then (1 : ℂ) else 0)) • (1 : A) + E a b := by
  rw [shiftedGenerator_eq_ite_smul_add, ite_zero_eq_mul_ite]

lemma shiftedGenerator_quadratic {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (x y : ℂ) (hxy : x - y = 1) (p q c d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d + Tm E x p d * Tm E y q c
      - Tm E x q d * Tm E y p c = 0 := by
  have hx : x = y + 1 := eq_add_of_sub_eq' hxy
  subst hx
  have h1 : E p c * E q d = E q d * E p c + ((if q = c then (1 : ℂ) else 0) • E p d
      - (if p = d then (1 : ℂ) else 0) • E q c) := by
    rw [eq_add_of_sub_eq' (hE p c q d)]
    congr 1
    rcases eq_or_ne c q with h | h
    · subst h
      rcases eq_or_ne d p with h' | h'
      · subst h'; simp
      · simp [h', h'.symm]
    · rcases eq_or_ne d p with h' | h'
      · subst h'; simp [h, h.symm]
      · simp [h, h.symm, h', h'.symm]
  have h2 : E p d * E q c = E q c * E p d + ((if q = d then (1 : ℂ) else 0) • E p c
      - (if p = c then (1 : ℂ) else 0) • E q d) := by
    rw [eq_add_of_sub_eq' (hE p d q c)]
    congr 1
    rcases eq_or_ne d q with h | h
    · subst h
      rcases eq_or_ne c p with h' | h'
      · subst h'; simp
      · simp [h', h'.symm]
    · rcases eq_or_ne c p with h' | h'
      · subst h'; simp [h, h.symm]
      · simp [h, h.symm, h', h'.symm]
  simp only [Tm_eq_smul_one_add]
  generalize (if p = c then (1 : ℂ) else 0) = δpc at h2 ⊢
  generalize (if q = d then (1 : ℂ) else 0) = δqd at h2 ⊢
  generalize (if q = c then (1 : ℂ) else 0) = δqc at h1 ⊢
  generalize (if p = d then (1 : ℂ) else 0) = δpd at h1 ⊢
  generalize E p c = Epc at h1 h2 ⊢
  generalize E q d = Eqd at h1 h2 ⊢
  generalize E q c = Eqc at h1 h2 ⊢
  generalize E p d = Epd at h1 h2 ⊢
  simp only [add_mul, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [h1, h2]
  module

lemma prod_ofFn_split_pair {M : Type*} [Monoid M] {t : ℕ} (f : Fin t → M) (i : ℕ) (hi : i + 1 < t) :
    (List.ofFn f).prod = ((List.ofFn f).take i).prod * (f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩) *
      ((List.ofFn f).drop (i + 2)).prod := by
  have h0 : i < (List.ofFn f).length := by simp; omega
  have h1 : i + 1 < (List.ofFn f).length := by simp; omega
  conv_lhs => rw [← List.take_append_drop i (List.ofFn f)]
  rw [List.prod_append, List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1,
    show i + 2 = i + 1 + 1 from rfl]
  simp only [List.prod_cons, List.getElem_ofFn, mul_assoc]

lemma take_ofFn_congr {α : Type*} {t : ℕ} (f g : Fin t → α) (i : ℕ)
    (h : ∀ k : Fin t, (k : ℕ) < i → f k = g k) :
    (List.ofFn f).take i = (List.ofFn g).take i := by
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h
    simp only [List.length_take, List.length_ofFn] at hk₁
    show k < i
    omega

lemma drop_ofFn_congr {α : Type*} {t : ℕ} (f g : Fin t → α) (i : ℕ)
    (h : ∀ k : Fin t, i ≤ (k : ℕ) → f k = g k) :
    (List.ofFn f).drop i = (List.ofFn g).drop i := by
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    simp only [List.getElem_drop, List.getElem_ofFn]
    apply h
    exact Nat.le_add_right _ _

lemma sandwich_alternating_sum {A : Type*} [Ring A] (L R a1 a2 a3 a4 : A) :
    L * a1 * R - L * a2 * R + L * a3 * R - L * a4 * R = L * (a1 - a2 + a3 - a4) * R := by
  simp only [mul_sub, mul_add, sub_mul, add_mul]

lemma prod_ofFn_alternating_sum {A : Type*} [Ring A] {t : ℕ} (f₁ f₂ f₃ f₄ : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h₂ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₂ k = f₁ k)
    (h₃ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₃ k = f₁ k)
    (h₄ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₄ k = f₁ k)
    (hmid : f₁ ⟨i, by omega⟩ * f₁ ⟨i + 1, hi⟩ - f₂ ⟨i, by omega⟩ * f₂ ⟨i + 1, hi⟩
      + f₃ ⟨i, by omega⟩ * f₃ ⟨i + 1, hi⟩ - f₄ ⟨i, by omega⟩ * f₄ ⟨i + 1, hi⟩ = 0) :
    (List.ofFn f₁).prod - (List.ofFn f₂).prod + (List.ofFn f₃).prod - (List.ofFn f₄).prod = 0 := by
  rw [prod_ofFn_split_pair f₁ i hi, prod_ofFn_split_pair f₂ i hi, prod_ofFn_split_pair f₃ i hi,
    prod_ofFn_split_pair f₄ i hi,
    take_ofFn_congr f₂ f₁ i (fun k hk => h₂ k (by omega) (by omega)),
    take_ofFn_congr f₃ f₁ i (fun k hk => h₃ k (by omega) (by omega)),
    take_ofFn_congr f₄ f₁ i (fun k hk => h₄ k (by omega) (by omega)),
    drop_ofFn_congr f₂ f₁ (i + 2) (fun k hk => h₂ k (by omega) (by omega)),
    drop_ofFn_congr f₃ f₁ (i + 2) (fun k hk => h₃ k (by omega) (by omega)),
    drop_ofFn_congr f₄ f₁ (i + 2) (fun k hk => h₄ k (by omega) (by omega)),
    sandwich_alternating_sum, hmid, mul_zero, zero_mul]

def exchangeTwo_self_eq_one {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin t)) : A :=
  (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (a (σ k)) (b k)).prod

lemma quantumMinor_eq_sum_term {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) :
    qminor E a b u = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * exchangeTwo_self_eq_one E a b u σ := rfl

lemma quantumMinorTerm_adjacent_swap {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1))) :
    exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
      + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
      - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) = 0 := by
  unfold exchangeTwo_self_eq_one
  have hi : (i : ℕ) + 1 < m + 1 := by omega
  have hfix : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 →
      Equiv.swap i.castSucc i.succ k = k := by
    intro k hk₁ hk₂
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hk₁ (by rw [h, Fin.val_castSucc]))
      (fun h => hk₂ (by rw [h, Fin.val_succ]))
  refine prod_ofFn_alternating_sum _ _ _ _ (i : ℕ) hi ?_ ?_ ?_ ?_
  · intro k hk₁ hk₂
    simp only [Equiv.Perm.mul_apply, hfix k hk₁ hk₂]
  · intro k hk₁ hk₂
    simp only [Function.comp_apply, hfix k hk₁ hk₂]
  · intro k hk₁ hk₂
    simp only [Equiv.Perm.mul_apply, Function.comp_apply, hfix k hk₁ hk₂]
  · have key := shiftedGenerator_quadratic E hE (u - ((i : ℕ) : ℂ)) (u - (((i : ℕ) + 1 : ℕ) : ℂ))
      (by push_cast; ring) (a (σ i.castSucc)) (a (σ i.succ)) (b i.castSucc) (b i.succ)
    have e0 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := rfl
    have e1 : (⟨(i : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ := rfl
    simp only [e0, e1, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    exact key

lemma eq_zero_of_add_self_eq_zero {A : Type*} [Ring A] [Algebra ℂ A] (X : A) (h : X + X = 0) : X = 0 := by
  calc X = ((2 : ℂ)⁻¹ * 2) • X := by rw [inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = (2 : ℂ)⁻¹ • (X + X) := by rw [mul_smul, two_smul]
    _ = 0 := by rw [h, smul_zero]

lemma quantumMinor_adjacent_col_swap {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) :
    qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u = - qminor E a b u := by
  have hsgn : Equiv.Perm.sign (Equiv.swap i.castSucc i.succ) = -1 :=
    Equiv.Perm.sign_swap (ne_of_lt Fin.castSucc_lt_succ)
  have reindex : ∀ bb : Fin (m + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
        exchangeTwo_self_eq_one E a bb u (σ * Equiv.swap i.castSucc i.succ) = - qminor E a bb u := by
    intro bb
    rw [quantumMinor_eq_sum_term, ← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i.castSucc i.succ)) _ _ (fun σ => ?_)
    simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, hsgn, Units.val_neg, Int.cast_neg, mul_neg,
      mul_one, neg_mul, neg_neg]
  have hsum : ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
      (exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
        + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
        - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ)) = 0 := by
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    rw [quantumMinorTerm_adjacent_swap E hE a b i u σ, mul_zero]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [reindex, reindex, ← quantumMinor_eq_sum_term, ← quantumMinor_eq_sum_term] at hsum
  have hX : qminor E a b u + qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u = 0 := by
    apply eq_zero_of_add_self_eq_zero
    convert hsum using 1
    abel
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hX

theorem quantumMinorColSkew_holds : QSkewCol := by
  intro A _ _ n t E hE a b τ u
  cases t with
  | zero =>
    have hτ : τ = 1 := Subsingleton.elim _ _
    subst hτ
    simp
  | succ m =>
    have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top τ
    revert b
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro b
      have hs : i.castSucc ≠ i.succ := ne_of_lt Fin.castSucc_lt_succ
      rw [quantumMinor_adjacent_col_swap E hE a b i u, Equiv.Perm.sign_swap hs]
      simp
    | one =>
      intro b
      simp
    | mul x y _ _ hx hy =>
      intro b
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy (b ∘ ⇑x), hx b, ← mul_assoc,
        Equiv.Perm.sign_mul, mul_comm (Equiv.Perm.sign x), Units.val_mul, Int.cast_mul]

end Formalism.REAL
