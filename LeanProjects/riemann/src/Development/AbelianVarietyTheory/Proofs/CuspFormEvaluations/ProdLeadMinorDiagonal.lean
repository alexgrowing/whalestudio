import Mathlib

open MvPolynomial Matrix

namespace GlobalTheory

namespace UnipotentInvariant

variable {K : Type*} [Field K] {p : ℕ}

def rowAdd (a b : Fin p) (t : K) (M : Matrix (Fin p) (Fin p) K) : Matrix (Fin p) (Fin p) K :=
  Matrix.of fun i k => M i k + if i = b then t * M a k else 0

def BiInvariant (f : Matrix (Fin p) (Fin p) K → K) : Prop :=
  (∀ a b : Fin p, a < b → ∀ t M, f (rowAdd a b t M) = f M) ∧
  (∀ a b : Fin p, a < b → ∀ t M, f (rowAdd a b t M)ᵀ = f Mᵀ)

theorem BiInvariant.transpose {f : Matrix (Fin p) (Fin p) K → K} (h : BiInvariant f) :
    BiInvariant fun M => f Mᵀ :=
  ⟨h.2, fun a b hab t M => by simpa using h.1 a b hab t M⟩

def leadMinor (i : Fin p) (M : Matrix (Fin p) (Fin p) K) : K :=
  (Matrix.of fun a b : Fin (i.val + 1) => M (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)).det

theorem leadMinor_transpose (i : Fin p) (M : Matrix (Fin p) (Fin p) K) :
    leadMinor i Mᵀ = leadMinor i M := by
  unfold leadMinor
  rw [← det_transpose]
  rfl

theorem leadMinor_rowAdd (i a b : Fin p) (hab : a < b) (t : K) (M : Matrix (Fin p) (Fin p) K) :
    leadMinor i (rowAdd a b t M) = leadMinor i M := by
  unfold leadMinor
  by_cases hb : b.val < i.val + 1
  · have ha : a.val < i.val + 1 := lt_trans hab hb
    have hne : (⟨b.val, hb⟩ : Fin (i.val + 1)) ≠ ⟨a.val, ha⟩ := by
      intro h
      have : b.val = a.val := Fin.mk.inj h
      exact absurd hab (by simp [Fin.lt_def, this])
    rw [← det_updateRow_add_smul_self
      (Matrix.of fun a b : Fin (i.val + 1) => M (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)) hne t]
    congr 1
    ext u v
    by_cases hu : u = ⟨b.val, hb⟩
    · subst hu
      simp [rowAdd, Fin.castLE]
    · have : Fin.castLE i.isLt u ≠ b := by
        intro h
        apply hu
        ext
        simpa using congrArg Fin.val h
      simp [rowAdd, updateRow_ne hu, this]
  · congr 1
    ext u v
    have : Fin.castLE i.isLt u ≠ b := by
      intro h
      apply hb
      rw [← h]
      exact u.isLt
    simp [rowAdd, this]

theorem biInvariant_leadMinor (i : Fin p) : BiInvariant (K := K) (leadMinor i) :=
  ⟨leadMinor_rowAdd i, fun a b hab t M => by
    rw [leadMinor_transpose, leadMinor_transpose, leadMinor_rowAdd i a b hab]⟩

theorem BiInvariant.what₂ {f : Matrix (Fin p) (Fin p) K → K} (h : BiInvariant f) (n : Fin p)
    (t : Fin p → K) (M : Matrix (Fin p) (Fin p) K) (S : Finset (Fin p)) (hS : ∀ b ∈ S, n < b) :
    f (Matrix.of fun b k => M b k + if b ∈ S then t b * M n k else 0) = f M := by
  induction S using Finset.induction_on with
  | empty =>
    congr 1
    ext b k
    simp
  | insert b S hb ih =>
    have hn : n ∉ S := fun hh => lt_irrefl _ (hS n (Finset.mem_insert_of_mem hh))
    rw [← ih fun b hb => hS b (Finset.mem_insert_of_mem hb),
      ← h.1 n b (hS b (Finset.mem_insert_self _ _)) (t b)
        (Matrix.of fun b k => M b k + if b ∈ S then t b * M n k else 0)]
    congr 1
    ext u k
    by_cases hu : u = b
    · subst hu
      simp [rowAdd, hb, hn]
    · simp [rowAdd, hu]

theorem exists_clear_col (n : Fin p) (M : Matrix (Fin p) (Fin p) K) (hn : M n n ≠ 0) :
    ∃ M' : Matrix (Fin p) (Fin p) K, (∀ f, BiInvariant f → f M' = f M) ∧
      (∀ b, n < b → M' b n = 0) ∧ (∀ b k, b ≤ n → M' b k = M b k) ∧
      (∀ b k, M n k = 0 → M' b k = M b k) := by
  refine ⟨Matrix.of fun b k => M b k +
      if b ∈ Finset.Ioi n then (- M b n / M n n) * M n k else 0, fun f hf => ?_, ?_, ?_, ?_⟩
  · exact hf.what₂ n (fun b => - M b n / M n n) M _ (by simp)
  · intro b hb
    simp only [of_apply, Finset.mem_Ioi, hb, if_true]
    field_simp
    ring
  · intro b k hb
    simp [not_lt.mpr hb]
  · intro b k hk
    simp [hk]

theorem exists_cleared (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) (n : ℕ) :
    ∃ M' : Matrix (Fin p) (Fin p) K, (∀ f, BiInvariant f → f M' = f M) ∧
      ∀ i j : Fin p, i ≠ j → (i.val < n ∨ j.val < n) → M' i j = 0 := by
  induction n with
  | zero => exact ⟨M, fun _ _ => rfl, by simp⟩
  | succ n ih =>
    obtain ⟨M₀, h₀, hz₀⟩ := ih
    by_cases hn : n < p
    swap
    · exact ⟨M₀, h₀, fun i j hij _ => hz₀ i j hij (Or.inl (by omega))⟩
    set N : Fin p := ⟨n, hn⟩ with hN
    have hpiv : M₀ N N ≠ 0 := by
      intro h0
      apply hM N
      rw [← h₀ _ (biInvariant_leadMinor N)]
      unfold leadMinor
      apply det_eq_zero_of_row_eq_zero (Fin.last n)
      intro j
      simp only [of_apply]
      by_cases hj : j = Fin.last n
      · subst hj
        exact h0
      · apply hz₀
        · intro h
          apply hj
          ext
          simpa using (congrArg Fin.val h).symm
        · right
          exact Fin.val_lt_last hj
    obtain ⟨M₁, h₁, a₁, b₁, c₁⟩ := exists_clear_col N M₀ hpiv
    have hpiv₁ : M₁ᵀ N N ≠ 0 := by
      rw [transpose_apply, b₁ N N le_rfl]
      exact hpiv
    obtain ⟨M₂, h₂, a₂, b₂, c₂⟩ := exists_clear_col N M₁ᵀ hpiv₁
    have hz₁ : ∀ i j : Fin p, i ≠ j → (i.val < n ∨ j.val < n) → M₁ i j = 0 := by
      intro i j hij h
      rcases h with h | h
      · rw [b₁ i j (by simp [Fin.le_def, hN]; omega)]
        exact hz₀ i j hij (Or.inl h)
      · rw [c₁ i j (hz₀ N j (by intro hh; rw [← hh] at h; simp [hN] at h) (Or.inr h))]
        exact hz₀ i j hij (Or.inr h)
    have hcol : ∀ i : Fin p, i ≠ N → M₁ i N = 0 := by
      intro i hi
      rcases lt_or_gt_of_ne hi with h | h
      · exact hz₁ i N hi (Or.inl h)
      · exact a₁ i h
    refine ⟨M₂ᵀ, fun f hf => ?_, ?_⟩
    · have := h₂ _ hf.transpose
      simp only [transpose_transpose] at this
      rw [this, h₁ f hf, h₀ f hf]
    · intro i j hij h
      rw [transpose_apply]
      by_cases hj : j ≤ N
      · rw [b₂ j i hj, transpose_apply]
        rcases eq_or_lt_of_le hj with hj | hj
        · subst hj
          exact hcol i hij
        · exact hz₁ i j hij (Or.inr hj)
      · have hj' : N < j := not_le.mp hj
        have hi : i.val < n + 1 := by
          rcases h with h | h
          · exact h
          · exact absurd hj' (by simp [Fin.lt_def, hN]; omega)
        by_cases hiN : i = N
        · subst hiN
          exact a₂ j hj'
        · rw [c₂ j i (hcol i hiN), transpose_apply]
          refine hz₁ i j hij (Or.inl ?_)
          have : i.val ≠ n := fun hh => hiN (Fin.ext hh)
          omega

theorem exists_diagonal (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) :
    ∃ d : Fin p → K, ∀ f, BiInvariant f → f (diagonal d) = f M := by
  obtain ⟨M', h, hz⟩ := exists_cleared M hM p
  refine ⟨fun i => M' i i, fun f hf => ?_⟩
  rw [← h f hf]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij, hz i j hij (Or.inl i.isLt)]

theorem leadMinor_diagonal (i : Fin p) (d : Fin p → K) :
    leadMinor i (diagonal d) = ∏ a ∈ Finset.Iic i, d a := by
  unfold leadMinor
  have : (Matrix.of fun a b : Fin (i.val + 1) =>
      diagonal d (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)) =
      diagonal fun a => d (Fin.castLE i.isLt a) := by
    ext a b
    simp [diagonal_apply]
  rw [this, det_diagonal]
  refine Finset.prod_bij (fun a _ => Fin.castLE i.isLt a) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Finset.mem_Iic, Fin.le_def, Fin.val_castLE]
    omega
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro b hb
    simp only [Finset.mem_Iic, Fin.le_def] at hb
    exact ⟨⟨b.val, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

theorem prod_leadMinor_diagonal (d : Fin p → K) (c : Fin p → ℕ) :
    ∏ i, leadMinor i (diagonal d) ^ c i = ∏ a, d a ^ ∑ i ∈ Finset.Ici a, c i := by
  simp only [leadMinor_diagonal, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_comm' ?_
  intro x y
  simp

theorem BiInvariant.eq_mul_prod {f : Matrix (Fin p) (Fin p) K → K} (hf : BiInvariant f)
    (c : Fin p → ℕ)
    (hd : ∀ d, f (diagonal d) = f 1 * ∏ a, d a ^ ∑ i ∈ Finset.Ici a, c i)
    (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) :
    f M = f 1 * ∏ i, leadMinor i M ^ c i := by
  obtain ⟨d, h⟩ := exists_diagonal M hM
  rw [← h f hf, hd, ← prod_leadMinor_diagonal]
  simp only [h _ (biInvariant_leadMinor _)]

variable {σ : Type*} [DecidableEq σ]

noncomputable def setBlock (z : Fin p × Fin p → σ) (x : σ → K) (M : Matrix (Fin p) (Fin p) K) :
    σ → K :=
  Function.extend z (fun w => M w.1 w.2) x

omit [Field K] [DecidableEq σ] in
theorem setBlock_apply {z : Fin p × Fin p → σ} (hz : Function.Injective z) (x : σ → K)
    (M : Matrix (Fin p) (Fin p) K) (w : Fin p × Fin p) : setBlock z x M (z w) = M w.1 w.2 :=
  hz.extend_apply _ _ _

omit [Field K] [DecidableEq σ] in
theorem setBlock_of_not {z : Fin p × Fin p → σ} (x : σ → K)
    (M : Matrix (Fin p) (Fin p) K) {s : σ} (hs : ¬ ∃ w, z w = s) : setBlock z x M s = x s :=
  Function.extend_apply' _ _ _ hs

omit [DecidableEq σ] in
theorem eval_bind₁' (y : σ → K) (g : σ → MvPolynomial σ K) (P : MvPolynomial σ K) :
    eval y (bind₁ g P) = eval (fun s => eval y (g s)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P s hP => simp [hP]

theorem biInvariant_eval {z : Fin p × Fin p → σ} (hz : Function.Injective z)
    (P : MvPolynomial σ K)
    (hr : ∀ a b : Fin p, a < b → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (hc : ∀ k l : Fin p, k < l → ∀ t : K,
      bind₁ (fun s => X s + ∑ a, if s = z (a, l) then C t * X (z (a, k)) else 0) P = P)
    (x : σ → K) : BiInvariant fun M => eval (setBlock z x M) P := by
  constructor
  · intro a b hab t M
    beta_reduce
    conv_rhs => rw [← hr a b hab t, eval_bind₁']
    congr 2
    funext s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨⟨u, v⟩, rfl⟩ := hs
      simp only [setBlock_apply hz, map_add, eval_X, map_sum, hz.eq_iff, Prod.mk.injEq,
        apply_ite (eval (setBlock z x M)), map_mul, eval_C, map_zero, rowAdd, of_apply]
      by_cases hu : u = b <;> simp [hu]
    · have : ∀ w, s ≠ z w := fun w h => hs ⟨w, h.symm⟩
      simp [setBlock_of_not _ _ hs, this]
  · intro a b hab t M
    beta_reduce
    conv_rhs => rw [← hc a b hab t, eval_bind₁']
    congr 2
    funext s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨⟨u, v⟩, rfl⟩ := hs
      simp only [setBlock_apply hz, map_add, eval_X, map_sum, hz.eq_iff, Prod.mk.injEq,
        apply_ite (eval (setBlock z x Mᵀ)), map_mul, eval_C, map_zero, rowAdd, of_apply,
        transpose_apply]
      by_cases hu : v = b <;> simp [hu]
    · have : ∀ w, s ≠ z w := fun w h => hs ⟨w, h.symm⟩
      simp [setBlock_of_not _ _ hs, this]

theorem eval_setBlock_diagonal {z : Fin p × Fin p → σ} (hz : Function.Injective z)
    (P : MvPolynomial σ K) (l : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = l a) (x : σ → K) (d : Fin p → K) :
    eval (setBlock z x (diagonal d)) P = eval (setBlock z x 1) P * ∏ a, d a ^ l a := by
  let w : σ → K := setBlock z 1 (Matrix.of fun a _ => d a)
  have hw : ∀ s, setBlock z x (diagonal d) s = setBlock z x 1 s * w s := by
    intro s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨⟨u, v⟩, rfl⟩ := hs
      simp only [w, setBlock_apply hz, diagonal_apply, one_apply, of_apply]
      split_ifs <;> simp
    · simp [w, setBlock_of_not _ _ hs]
  rw [eval_eq, eval_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [hw, mul_pow, Finset.prod_mul_distrib, mul_assoc]
  congr 2
  have h1 : ∏ s ∈ m.support, w s ^ m s = ∏ s ∈ Finset.univ.image z, w s ^ m s := by
    refine Finset.prod_congr_of_eq_on_inter ?_ ?_ fun _ _ _ => rfl
    · intro s _ hs
      have hs' : ¬ ∃ w, z w = s := by simpa using hs
      simp [w, setBlock_of_not _ _ hs']
    · intro s _ hs
      rw [Finsupp.notMem_support_iff.mp hs, pow_zero]
  rw [h1, Finset.prod_image fun _ _ _ _ h => hz h, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← hrow a m hm, ← Finset.prod_pow_eq_pow_sum]
  simp [w, setBlock_apply hz]

end UnipotentInvariant

open UnipotentInvariant in

theorem eq_mul_prod_minors {K σ : Type*} [Field K] [CharZero K] [DecidableEq σ] {p : ℕ} (z : Fin p × Fin p → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) (c : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = ∑ i ∈ Finset.Ici a, c i)
    (hr : ∀ a b : Fin p, a < b → ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (hc : ∀ k l : Fin p, k < l → ∀ t : K, bind₁ (fun s => X s + ∑ a, if s = z (a, l) then C t * X (z (a, k)) else 0) P = P) :
    ∃ Q : MvPolynomial σ K, (∀ w, z w ∉ Q.vars) ∧
      P = Q * ∏ i : Fin p, (Matrix.of fun a b : Fin (i.val + 1) => (X (z (Fin.castLE i.isLt a, Fin.castLE i.isLt b)) : MvPolynomial σ K)).det ^ c i := by
  let g : σ → MvPolynomial σ K :=
    Function.extend z (fun w => C ((1 : Matrix (Fin p) (Fin p) K) w.1 w.2)) X
  let Δ : Fin p → MvPolynomial σ K := fun i => (Matrix.of fun a b : Fin (i.val + 1) =>
    (X (z (Fin.castLE i.isLt a, Fin.castLE i.isLt b)) : MvPolynomial σ K)).det
  have hΔ : ∀ (x : σ → K) i, eval x (Δ i) = leadMinor i (Matrix.of fun a b => x (z (a, b))) := by
    intro x i
    simp only [Δ, leadMinor]
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp
  have hg : ∀ x : σ → K, eval x (bind₁ g P) = eval (setBlock z x 1) P := by
    intro x
    rw [eval_bind₁']
    congr 2
    funext s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨w, rfl⟩ := hs
      simp [g, setBlock_apply hz, hz.extend_apply]
    · simp [g, setBlock_of_not _ _ hs, Function.extend_apply' _ _ _ hs]
  refine ⟨bind₁ g P, ?_, ?_⟩
  · intro w hw
    obtain ⟨s, -, hs'⟩ := mem_vars_bind₁ g P hw
    by_cases hs : ∃ w, z w = s
    · obtain ⟨w', rfl⟩ := hs
      simp [g, hz.extend_apply] at hs'
    · simp only [g, Function.extend_apply' _ _ _ hs, vars_X, Finset.mem_singleton] at hs'
      exact hs ⟨w, hs'⟩
  · have hne : ∏ i, Δ i ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ h => ?_
      have := hΔ (setBlock z 0 1) i
      rw [h, map_zero] at this
      have h1 : (Matrix.of fun a b => setBlock z (0 : σ → K) 1 (z (a, b))) = diagonal fun _ => 1 := by
        ext a b
        simp [setBlock_apply hz]
      rw [h1, leadMinor_diagonal] at this
      simp at this
    apply mul_left_cancel₀ hne
    apply MvPolynomial.funext
    intro x
    change eval x (_ * P) = eval x (_ * (_ * ∏ i, Δ i ^ c i))
    simp only [map_mul, map_prod, map_pow, hΔ, hg]
    by_cases h : ∀ i, leadMinor i (Matrix.of fun a b => x (z (a, b))) ≠ 0
    · congr 1
      have hx : setBlock z x (Matrix.of fun a b => x (z (a, b))) = x := by
        funext s
        by_cases hs : ∃ w, z w = s
        · obtain ⟨w, rfl⟩ := hs
          simp [setBlock_apply hz]
        · exact setBlock_of_not _ _ hs
      have := (biInvariant_eval hz P hr hc x).eq_mul_prod c
        (eval_setBlock_diagonal hz P _ hrow x) _ h
      simpa only [hx] using this
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul, zero_mul]

end GlobalTheory
