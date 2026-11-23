import Formalism.MahlerMeasure.LevelSum

namespace Formalism.GM

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)

theorem tieE_apply' (g : MvPolynomial σ k) :
    tieE w e g = (∑ c, X (w c) * X (e c)) * g := by
  rfl

theorem tieF_apply' (g : MvPolynomial σ k) :
    tieF w e g = ∑ c, pderiv (w c) (pderiv (e c) g) := by
  simp [tieF]

theorem coeff_X_mul_pderiv' (i : σ) (p : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (X i * pderiv i p) = coeff m p * (m i : k) := by
  classical
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro s a
    have key : X i * pderiv i (monomial s a : MvPolynomial σ k) = monomial s (a * (s i : k)) := by
      rw [pderiv_monomial]
      by_cases hs : s i = 0
      · simp [hs]
      · rw [show (X i : MvPolynomial σ k) = monomial (Finsupp.single i 1) 1 from rfl,
          monomial_mul, one_mul]
        have hsum : Finsupp.single i 1 + (s - Finsupp.single i 1) = s := by
          ext j
          by_cases hij : i = j
          · subst hij
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
            omega
          · simp [hij]
        rw [hsum]
    rw [key, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  · intro p q hp hq
    simp only [map_add, mul_add, coeff_add, hp, hq, add_mul]

theorem euler_w_of_biHom {a b : ℕ} {g : MvPolynomial σ k} (h : BiHom w e a b g) :
    (∑ c, X (w c) * pderiv (w c) g) = (a : k) • g := by
  ext m
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  simp_rw [coeff_X_mul_pderiv']
  rw [← Finset.mul_sum]
  by_cases hm : coeff m g = 0
  · rw [hm]; simp
  · obtain ⟨h1, -⟩ := h m (MvPolynomial.mem_support_iff.mpr hm)
    rw [← h1, Nat.cast_sum]
    ring

theorem euler_e_of_biHom {a b : ℕ} {g : MvPolynomial σ k} (h : BiHom w e a b g) :
    (∑ c, X (e c) * pderiv (e c) g) = (b : k) • g := by
  ext m
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  simp_rw [coeff_X_mul_pderiv']
  rw [← Finset.mul_sum]
  by_cases hm : coeff m g = 0
  · rw [hm]; simp
  · obtain ⟨-, h2⟩ := h m (MvPolynomial.mem_support_iff.mpr hm)
    rw [← h2, Nat.cast_sum]
    ring

variable {w e}

private theorem mvPolynomial_pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ k) = 0 := by
  exact pderiv_X_of_ne h

private theorem mvPolynomial_pderiv_X_self (i : σ) : pderiv i (X i : MvPolynomial σ k) = 1 := by
  exact pderiv_X_self i

theorem pderiv_X_inj {f : Fin r → σ} (hf : Function.Injective f) (c d : Fin r) :
    pderiv (f c) (X (f d) : MvPolynomial σ k) = if d = c then 1 else 0 := by
  by_cases h : d = c
  · subst h
    rw [if_pos rfl]
    exact mvPolynomial_pderiv_X_self _
  · rw [if_neg h]
    exact mvPolynomial_pderiv_X_of_ne (fun h' => h (hf h'))

theorem pderiv_e_S (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (c : Fin r) : pderiv (e c) (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = X (w c) := by
  have h0 : ∀ d, pderiv (e c) (X (w d) : MvPolynomial σ k) = 0 := fun d => mvPolynomial_pderiv_X_of_ne (hwe d c)
  rw [map_sum]
  simp only [Derivation.leibniz, h0, pderiv_X_inj he, smul_eq_mul, mul_ite, mul_one, mul_zero,
    add_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem pderiv_w_S (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d)
    (c : Fin r) : pderiv (w c) (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = X (e c) := by
  have h0 : ∀ d, pderiv (w c) (X (e d) : MvPolynomial σ k) = 0 :=
    fun d => mvPolynomial_pderiv_X_of_ne (fun h => hwe c d h.symm)
  rw [map_sum]
  simp only [Derivation.leibniz, h0, pderiv_X_inj hw, smul_eq_mul, mul_ite, mul_one, mul_zero,
    zero_add, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private theorem natCast_smul_eq_natCast_mul (n : ℕ) (g : MvPolynomial σ k) :
    (n : k) • g = (n : MvPolynomial σ k) * g := by
  rw [smul_eq_C_mul, map_natCast]

theorem F_S_mul (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (a b : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g)
    (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) :
    ∑ c, pderiv (w c) (pderiv (e c) ((∑ d, X (w d) * X (e d)) * g)) =
      (∑ d, X (w d) * X (e d)) * ∑ c, pderiv (w c) (pderiv (e c) g) + ((a + b + r : ℕ) : k) • g := by
  have h1 : ∀ c, pderiv (e c) ((∑ d, X (w d) * X (e d)) * g) =
      X (w c) * g + (∑ d, X (w d) * X (e d)) * pderiv (e c) g := by
    intro c
    rw [Derivation.leibniz, pderiv_e_S he hwe, smul_eq_mul, smul_eq_mul]
    ring
  have h2 : ∀ c, pderiv (w c) (X (w c) * g) = g + X (w c) * pderiv (w c) g := by
    intro c
    rw [Derivation.leibniz, mvPolynomial_pderiv_X_self, smul_eq_mul, smul_eq_mul]
    ring
  have h3 : ∀ c, pderiv (w c) ((∑ d, X (w d) * X (e d)) * pderiv (e c) g) =
      X (e c) * pderiv (e c) g + (∑ d, X (w d) * X (e d)) * pderiv (w c) (pderiv (e c) g) := by
    intro c
    rw [Derivation.leibniz, pderiv_w_S hw hwe, smul_eq_mul, smul_eq_mul]
    ring
  calc ∑ c, pderiv (w c) (pderiv (e c) ((∑ d, X (w d) * X (e d)) * g))
      = ∑ c, (g + (X (w c) * pderiv (w c) g + X (e c) * pderiv (e c) g) +
          (∑ d, X (w d) * X (e d)) * pderiv (w c) (pderiv (e c) g)) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [h1, map_add, h2, h3]
        ring
    _ = (∑ _c : Fin r, g) + ((∑ c, X (w c) * pderiv (w c) g) + ∑ c, X (e c) * pderiv (e c) g) +
          (∑ d, X (w d) * X (e d)) * ∑ c, pderiv (w c) (pderiv (e c) g) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
        rw [hW, hE]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, natCast_smul_eq_natCast_mul]
        push_cast
        ring

theorem euler_w_S_mul (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (a : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g) :
    ∑ c, X (w c) * pderiv (w c) ((∑ d, X (w d) * X (e d)) * g) =
      ((a + 1 : ℕ) : k) • ((∑ d, X (w d) * X (e d)) * g) := by
  have h1 : ∀ c, X (w c) * pderiv (w c) ((∑ d, X (w d) * X (e d)) * g) =
      X (w c) * X (e c) * g + (∑ d, X (w d) * X (e d)) * (X (w c) * pderiv (w c) g) := by
    intro c
    rw [Derivation.leibniz, pderiv_w_S hw hwe, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hW]
  simp only [natCast_smul_eq_natCast_mul]
  push_cast
  ring

theorem euler_e_S_mul (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (b : ℕ) (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) :
    ∑ c, X (e c) * pderiv (e c) ((∑ d, X (w d) * X (e d)) * g) =
      ((b + 1 : ℕ) : k) • ((∑ d, X (w d) * X (e d)) * g) := by
  have h1 : ∀ c, X (e c) * pderiv (e c) ((∑ d, X (w d) * X (e d)) * g) =
      X (w c) * X (e c) * g + (∑ d, X (w d) * X (e d)) * (X (e c) * pderiv (e c) g) := by
    intro c
    rw [Derivation.leibniz, pderiv_e_S he hwe, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hE]
  simp only [natCast_smul_eq_natCast_mul]
  push_cast
  ring

private theorem linearMap_pow_zero_apply (f : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (x : MvPolynomial σ k) :
    (f ^ 0) x = x := by
  rw [pow_zero]; first | done | rfl

private theorem linearMap_pow_succ_apply_eq_apply_pow (f : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (n : ℕ)
    (x : MvPolynomial σ k) : (f ^ (n + 1)) x = f ((f ^ n) x) := by
  rw [pow_succ']; first | done | rfl

private theorem tieE_pow_succ_apply (j : ℕ) (x : MvPolynomial σ k) :
    (tieE w e ^ (j + 1)) x = (∑ d, X (w d) * X (e d)) * (tieE w e ^ j) x := by
  rw [linearMap_pow_succ_apply_eq_apply_pow, tieE_apply']

theorem euler_pow (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (u : MvPolynomial σ k) (a b : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) u = (a : k) • u)
    (hE : ∑ c, X (e c) * pderiv (e c) u = (b : k) • u) (j : ℕ) :
    (∑ c, X (w c) * pderiv (w c) ((tieE w e ^ j) u) = ((a + j : ℕ) : k) • (tieE w e ^ j) u) ∧
    (∑ c, X (e c) * pderiv (e c) ((tieE w e ^ j) u) = ((b + j : ℕ) : k) • (tieE w e ^ j) u) := by
  induction j with
  | zero =>
    simp only [linearMap_pow_zero_apply, Nat.add_zero]
    exact ⟨hW, hE⟩
  | succ j ih =>
    rw [tieE_pow_succ_apply j u]
    refine ⟨?_, ?_⟩
    · rw [euler_w_S_mul hw hwe _ _ ih.1, Nat.add_assoc]
    · rw [euler_e_S_mul he hwe _ _ ih.2, Nat.add_assoc]

theorem F_E_pow (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (u : MvPolynomial σ k) (a b : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) u = (a : k) • u)
    (hE : ∑ c, X (e c) * pderiv (e c) u = (b : k) • u) (hF : tieF w e u = 0) (j : ℕ) :
    tieF w e ((tieE w e ^ (j + 1)) u) = (((j + 1) * (a + b + r + j) : ℕ) : k) • (tieE w e ^ j) u := by
  induction j with
  | zero =>
    rw [tieE_pow_succ_apply 0 u, linearMap_pow_zero_apply, tieF_apply', F_S_mul hw he hwe u a b hW hE,
      ← tieF_apply' w e u, hF]
    simp only [natCast_smul_eq_natCast_mul]
    push_cast
    ring
  | succ j ih =>
    obtain ⟨h1, h2⟩ := euler_pow hw he hwe u a b hW hE (j + 1)
    rw [tieE_pow_succ_apply (j + 1) u, tieF_apply', F_S_mul hw he hwe _ _ _ h1 h2,
      ← tieF_apply' w e ((tieE w e ^ (j + 1)) u), ih, tieE_pow_succ_apply j u]
    simp only [natCast_smul_eq_natCast_mul]
    push_cast
    ring

private theorem linearMap_pow_succ_apply_eq_pow_apply (f : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (n : ℕ)
    (x : MvPolynomial σ k) : (f ^ (n + 1)) x = (f ^ n) (f x) := by
  rw [pow_succ]; first | done | rfl

private theorem linearMap_pow_apply_pow_apply (f : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (m n : ℕ)
    (x : MvPolynomial σ k) : (f ^ m) ((f ^ n) x) = (f ^ (m + n)) x := by
  rw [pow_add]; first | done | rfl

theorem F_pow_E_pow (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (u : MvPolynomial σ k) (a b N0 : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) u = (a : k) • u)
    (hE : ∑ c, X (e c) * pderiv (e c) u = (b : k) • u) (hF : tieF w e u = 0) (hN : a + b + r = N0 + 1)
    (j l : ℕ) :
    (tieF w e ^ j) ((tieE w e ^ l) u) =
      ((l.descFactorial j * (N0 + l).descFactorial j : ℕ) : k) • (tieE w e ^ (l - j)) u := by
  induction j generalizing l with
  | zero =>
    simp only [linearMap_pow_zero_apply, Nat.descFactorial_zero, mul_one, Nat.cast_one, one_smul, Nat.sub_zero]
  | succ j ih =>
    cases l with
    | zero =>
      rw [linearMap_pow_succ_apply_eq_pow_apply, linearMap_pow_zero_apply, hF, map_zero, Nat.zero_descFactorial_succ, zero_mul,
        Nat.cast_zero, zero_smul]
    | succ l =>
      rw [linearMap_pow_succ_apply_eq_pow_apply, F_E_pow hw he hwe u a b hW hE hF l, map_smul, ih l, smul_smul,
        ← Nat.cast_mul, Nat.add_sub_add_right]
      congr 2
      rw [hN, Nat.succ_descFactorial_succ, show N0 + (l + 1) = N0 + l + 1 by omega, Nat.succ_descFactorial_succ]
      ring

end

theorem levelAct_of (hS : LevelSum) : LevelAct := by
  intro k σ _ _ r w e hw he hwe hr o n z l u hlo hln hF hB
  have hW := euler_w_of_biHom w e hB
  have hE := euler_e_of_biHom w e hB
  obtain ⟨N0, hN⟩ : ∃ N0, o - l + (n - l) + r = N0 + 1 := ⟨o - l + (n - l) + r - 1, by omega⟩
  have key : ∀ j, ((tieE w e ^ j).comp (tieF w e ^ j)) ((tieE w e ^ l) u) =
      ((l.descFactorial j * (N0 + l).descFactorial j : ℕ) : k) • (tieE w e ^ l) u := by
    intro j
    rw [LinearMap.comp_apply, F_pow_E_pow hw he hwe u (o - l) (n - l) N0 hW hE hF hN j l, map_smul]
    by_cases hjl : j ≤ l
    · congr 1
      rw [linearMap_pow_apply_pow_apply, show j + (l - j) = l by omega]
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr (show l < j by omega)]
  have hA : z + l ≤ o + n + r + z - 1 := by omega
  have hS' := hS (o + n + r + z - 1) z l hA
  rw [show o + n + r + z - 1 - z - l = N0 + l by omega] at hS'
  have hcast := congrArg (Rat.cast : ℚ → k) hS'
  simp only [qch, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Rat.cast_natCast] at hcast
  simp only [tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, key, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Finset.sum_subset (Finset.range_mono (show l + 1 ≤ o + 1 by omega)) ?_]
  · refine Eq.trans ?_ hcast
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjl : j ≤ l := by
      rw [Finset.mem_range] at hj
      omega
    have hf : ((j.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hc : (((o + n + r + z - 1).choose j : ℕ) : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
  · intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr (show l < j by omega)]

end Formalism.GM
