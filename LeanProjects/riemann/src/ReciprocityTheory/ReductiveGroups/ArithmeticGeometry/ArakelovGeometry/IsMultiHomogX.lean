import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def lg (J : Ideal (MRing ι)) (a : K → ℕ) : ℝ := Real.log (Nat.card (mPiece J a))

def tdeg (a : K → ℕ) : ℕ := ∑ k, a k

theorem lg_nonneg (J : Ideal (MRing ι)) (a : K → ℕ) : 0 ≤ lg J a := by
  unfold lg
  rcases Nat.eq_zero_or_pos (Nat.card (mPiece J a)) with h | h
  · rw [h]; simp
  · exact Real.log_nonneg (Nat.one_le_cast.mpr h)

theorem tdeg_sub_le (a c : K → ℕ) : tdeg (a - c) ≤ tdeg a := by
  unfold tdeg
  exact Finset.sum_le_sum fun k _ => Nat.sub_le (a k) (c k)

theorem nrm_natCast [DecidableEq K] (a : K → ℕ) : nrm (fun k => (a k : ℤ)) = (tdeg a : ℝ) := by
  simp [nrm, tdeg, Nat.cast_sum]

theorem pow_tdeg_mono {a b : K → ℕ} (h : tdeg a ≤ tdeg b) (m : ℕ) :
    ((tdeg a : ℝ) + 1) ^ m ≤ ((tdeg b : ℝ) + 1) ^ m := by
  have h' : (tdeg a : ℝ) ≤ tdeg b := by exact_mod_cast h
  gcongr

theorem isMultiHomog_X' [DecidableEq K] (b : K) (i : ι b) :
    IsMultiHomog (X ⟨b, i⟩ : MRing ι) (Pi.single b 1) := by
  intro m hm k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k = b
  · subst hk
    simp only [Pi.single_eq_same]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      apply Finsupp.single_eq_of_ne
      intro h
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact hj (by first | exact h.symm | exact h)
    · intro h; exact absurd (Finset.mem_univ i) h
  · simp [Finsupp.single_apply, hk, Ne.symm hk]

theorem lg_step {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) {q : Ideal (MRing ι)} (hq : ∀ g, g ∈ q ↔ g * f ∈ J) {a : K → ℕ}
    (hca : ∀ k, c k ≤ a k) {p : ℕ} (hp : 0 < p) (hpJ : (p : MRing ι) ∈ J) :
    lg J a = lg (J ⊔ Ideal.span {f}) a + lg q (a - c) := by
  have hpq : (p : MRing ι) ∈ q := (hq _).mpr (J.mul_mem_right _ hpJ)
  rw [lg, card_mPiece_step hJ hf hq hca, Nat.cast_mul, Real.log_mul, lg, lg]
  · exact_mod_cast (card_mPiece_pos _ a hp (Ideal.mem_sup_left hpJ)).ne'
  · exact_mod_cast (card_mPiece_pos _ _ hp hpq).ne'

theorem lg_chain (a : K → ℕ) {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    {c : Fin N → K → ℕ} {q : Fin N → Ideal (MRing ι)} (h0 : IsMultiHomogIdeal (F 0))
    (hlast : F (Fin.last N) = ⊤)
    (hj : ∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc)
    (ha : ∀ j k, c j k ≤ a k) {p : ℕ} (hp : 0 < p) (hpq : ∀ j, (p : MRing ι) ∈ q j) :
    lg (F 0) a = ∑ j, lg (q j) (a - c j) := by
  rw [lg, card_mPiece_chain a N F f c q h0 hlast hj ha, Nat.cast_prod, Real.log_prod]
  · rfl
  · intro j _
    exact_mod_cast (card_mPiece_pos _ _ hp (hpq j)).ne'

theorem walk_bound [DecidableEq K] (Δ : (K → ℕ) → ℝ) (a₁ m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ a : K → ℕ, ∀ b, (∀ k, a₁ ≤ a k) → a₁ < a b →
      |Δ a - Δ (a - Pi.single b 1)| ≤ B * m * ((tdeg a : ℝ) + 1) ^ (m - 1)) :
    ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) →
      |Δ a| ≤ |Δ (fun _ => a₁)| + B * m * tdeg a * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
  have hnn : ∀ a : K → ℕ, 0 ≤ B * m * (tdeg a : ℝ) * ((tdeg a : ℝ) + 1) ^ (m - 1) := fun a =>
    mul_nonneg (mul_nonneg (mul_nonneg hB (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (pow_nonneg (by positivity) _)
  have hconst : ∀ a : K → ℕ, (∀ k, a k ≤ a₁) → (∀ k, a₁ ≤ a k) →
      |Δ a| ≤ |Δ (fun _ => a₁)| + B * m * tdeg a * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
    intro a h1 h2
    have hc : a = fun _ => a₁ := funext fun k => le_antisymm (h1 k) (h2 k)
    subst hc
    linarith [hnn (fun _ => a₁)]
  intro a ha
  obtain ⟨n, hn⟩ : ∃ n, tdeg a = n := ⟨_, rfl⟩
  induction n generalizing a with
  | zero =>
    apply hconst a _ ha
    intro k
    have hk : a k ≤ tdeg a := by
      unfold tdeg
      exact Finset.single_le_sum (f := a) (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
    have := ha k
    omega
  | succ n ih =>
    by_cases hex : ∃ b, a₁ < a b
    · obtain ⟨b, hb⟩ := hex
      obtain ⟨a', ha'⟩ : ∃ a' : K → ℕ, a' = a - Pi.single b 1 := ⟨_, rfl⟩
      have ha'k : ∀ k, a' k + (Pi.single b 1 : K → ℕ) k = a k := by
        intro k
        rw [ha', Pi.sub_apply]
        apply Nat.sub_add_cancel
        by_cases hk : k = b
        · subst hk; simp; omega
        · simp [Pi.single_eq_of_ne hk]
      have ha'1 : ∀ k, a₁ ≤ a' k := by
        intro k
        have e := ha'k k
        by_cases hk : k = b
        · subst hk; simp at e; omega
        · simp [Pi.single_eq_of_ne hk] at e; rw [e]; exact ha k
      have htd : tdeg a' + 1 = tdeg a := by
        have h1 : ∑ k, (Pi.single b 1 : K → ℕ) k = 1 := by simp
        calc tdeg a' + 1 = ∑ k, a' k + ∑ k, (Pi.single b 1 : K → ℕ) k := by rw [h1]; rfl
          _ = ∑ k, a k := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun k _ => ha'k k
          _ = tdeg a := rfl
      have IH := ih a' ha'1 (by omega)
      have hs := hstep a b ha hb
      rw [← ha'] at hs
      have hmono : ((tdeg a' : ℝ) + 1) ^ (m - 1) ≤ ((tdeg a : ℝ) + 1) ^ (m - 1) :=
        pow_tdeg_mono (by omega) _
      have hT : (tdeg a : ℝ) = tdeg a' + 1 := by rw [← htd]; push_cast; ring
      have hBm : 0 ≤ B * m * (tdeg a' : ℝ) :=
        mul_nonneg (mul_nonneg hB (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      have key := mul_le_mul_of_nonneg_left hmono hBm
      generalize ((tdeg a : ℝ) + 1) ^ (m - 1) = P at hs key ⊢
      generalize ((tdeg a' : ℝ) + 1) ^ (m - 1) = P' at IH key
      have tri := abs_sub_abs_le_abs_sub (Δ a) (Δ a')
      rw [hT]
      nlinarith
    · push_neg at hex
      exact hconst a hex ha

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
