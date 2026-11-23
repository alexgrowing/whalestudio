import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelDecomp
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.ScalSum

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)

theorem mulLeft_pow_apply (a f : MvPolynomial σ k) (m : ℕ) :
    ((LinearMap.mulLeft k a) ^ m) f = a ^ m * f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ' a m, mul_assoc, ← ih, pow_succ']
    show LinearMap.mulLeft k a ((LinearMap.mulLeft k a ^ m) f) = _
    rw [LinearMap.mulLeft_apply]

private lemma pderiv_mul_of_pderiv_eq_zero (i : σ) (q f : MvPolynomial σ k) (h : pderiv i q = 0) :
    pderiv i (q * f) = q * pderiv i f := by
  rw [Derivation.leibniz, h, smul_zero, add_zero, smul_eq_mul]

theorem tieF_mul_free (q f : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) q = 0) (he : ∀ c, pderiv (e c) q = 0) :
    tieF w e (q * f) = q * tieF w e f := by
  have key : ∀ g : MvPolynomial σ k, tieF w e g = ∑ c, pderiv (w c) (pderiv (e c) g) := by
    intro g
    simp [tieF]
  rw [key, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pderiv_mul_of_pderiv_eq_zero _ _ _ (he c), pderiv_mul_of_pderiv_eq_zero _ _ _ (hw c)]

theorem tieF_pow_mul_free (q f : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) q = 0)
    (he : ∀ c, pderiv (e c) q = 0) (m : ℕ) :
    (tieF w e ^ m) (q * f) = q * (tieF w e ^ m) f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    show tieF w e ((tieF w e ^ m) (q * f)) = q * tieF w e ((tieF w e ^ m) f)
    rw [ih, tieF_mul_free w e q _ hw he]

noncomputable def ehP : MvPolynomial σ k := X zv * X sv + ∑ c, X (w c) * X (e c)

private lemma pderiv_X_pow_of_ne' (i j : σ) (h : i ≠ j) (n : ℕ) : pderiv i (X j ^ n : MvPolynomial σ k) = 0 := by
  classical
  rw [Derivation.leibniz_pow]
  simp [pderiv_X, Pi.single_apply, Ne.symm h]

theorem harmonicProjection_expand (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k) :
    M.tieP w e zv sv o n z x = ∑ m ∈ range (o + 1),
      (((-1 : k) ^ m) / (((m.factorial : k) ^ 2) * ((o + n + r + z - 1).choose m : k))) •
        (ehP w e zv sv ^ m * (X zv ^ z * (tieF w e ^ m) x)) := by
  have hE : ∀ (m : ℕ) (y : MvPolynomial σ k),
      (M.tieEh w e zv sv ^ m) y = ehP w e zv sv ^ m * y := by
    intro m y
    unfold M.tieEh
    exact mulLeft_pow_apply _ _ m
  unfold M.tieP
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [tieF_pow_mul_free w e _ x (fun c => pderiv_X_pow_of_ne' _ _ (hz c).1 z)
    (fun c => pderiv_X_pow_of_ne' _ _ (hz c).2 z) m, hE]

private lemma add_single_mem_support_of_mem_support_pderiv (i : σ) (p : MvPolynomial σ k) (t : σ →₀ ℕ) (ht : t ∈ (pderiv i p).support) :
    t + Finsupp.single i 1 ∈ p.support := by
  classical
  have hp : pderiv i p = ∑ s ∈ p.support, pderiv i (monomial s (coeff s p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [MvPolynomial.mem_support_iff, hp, MvPolynomial.coeff_sum] at ht
  obtain ⟨s, hs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  rw [pderiv_monomial, MvPolynomial.coeff_monomial] at hne
  split_ifs at hne with hst
  · have hsi : s i ≠ 0 := by
      intro h0
      apply hne
      rw [h0]
      simp
    have hts : t + Finsupp.single i 1 = s := by
      rw [← hst]
      ext j
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h
        omega
      · omega
    rw [hts]
    exact hs
  · exact absurd rfl hne

theorem tieF_pow_apply_eq_zero_of_min_lt [CharZero k] (hw : Function.Injective w) (he : Function.Injective e)
    (hwe : ∀ c d, w c ≠ e d) {o n : ℕ} {x : MvPolynomial σ k} (hx : BiHom w e o n x) :
    ∀ m, min o n < m → (tieF w e ^ m) x = 0 := by
  classical
  have hsupp : ∀ (y : MvPolynomial σ k) (t : σ →₀ ℕ), t ∈ (tieF w e y).support →
      ∃ c, t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 ∈ y.support := by
    intro y t ht
    have key : tieF w e y = ∑ c, pderiv (w c) (pderiv (e c) y) := by simp [tieF]
    rw [key] at ht
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
    exact ⟨c, add_single_mem_support_of_mem_support_pderiv _ _ _ (add_single_mem_support_of_mem_support_pderiv _ _ _ hc)⟩
  have hW1 : ∀ (t : σ →₀ ℕ) (c : Fin r),
      (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (w d)) = (∑ d, t (w d)) + 1 := by
    intro t c
    have h1 : ∀ d, (e c = w d) ↔ False := fun d => ⟨fun h => hwe d c h.symm, False.elim⟩
    simp [Finsupp.single_apply, hw.eq_iff, Finset.sum_add_distrib, h1]
  have hE1 : ∀ (t : σ →₀ ℕ) (c : Fin r),
      (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (e d)) = (∑ d, t (e d)) + 1 := by
    intro t c
    have h1 : ∀ d, (w c = e d) ↔ False := fun d => ⟨fun h => hwe c d h, False.elim⟩
    simp [Finsupp.single_apply, he.eq_iff, Finset.sum_add_distrib, h1]
  have claim : ∀ (j : ℕ) (t : σ →₀ ℕ), t ∈ ((tieF w e ^ j) x).support →
      (∑ d, t (w d)) + j = o ∧ (∑ d, t (e d)) + j = n := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have ht' : t ∈ x.support := by simpa using ht
      simpa using hx t ht'
    | succ j ih =>
      intro t ht
      have ht' : t ∈ (tieF w e ((tieF w e ^ j) x)).support := by
        rw [pow_succ'] at ht
        exact ht
      obtain ⟨c, hc⟩ := hsupp _ t ht'
      obtain ⟨h1, h2⟩ := ih _ hc
      rw [hW1] at h1
      rw [hE1] at h2
      constructor <;> omega
  intro m hm
  by_contra hne
  obtain ⟨t, ht⟩ := MvPolynomial.ne_zero_iff.mp hne
  obtain ⟨h1, h2⟩ := claim m t (MvPolynomial.mem_support_iff.mpr ht)
  omega

private lemma cast_choose_add_eq_factorial_div_of_charZero [CharZero k] (a b : ℕ) :
    (((a + b).choose b : ℕ) : k) = ((a + b).factorial : k) / ((a.factorial : k) * (b.factorial : k)) := by
  rw [eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)))]
  have h := Nat.add_choose_mul_factorial_mul_factorial a b
  rw [mul_assoc] at h
  exact_mod_cast h

private lemma factorial_choose_signed_sum_eq_zero [CharZero k] (N j : ℕ) (hj : 1 ≤ j) (hN : 2 * j + 1 ≤ N) :
    ∑ l ∈ range (j + 1), (-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((N - 2 * l - 1).choose (j - l) : k)) *
      ((l.factorial : k) ^ 2 * ((N - l).choose l : k))⁻¹ = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → k, ∀ l, c l = (-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 *
      ((N - 2 * l - 1).choose (j - l) : k)) * ((l.factorial : k) ^ 2 * ((N - l).choose l : k))⁻¹ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → k, ∀ l, W l = if l ≤ j then c l * (((l : ℕ) : k) * ((N - l - j : ℕ) : k)) /
      ((j : k) * ((N - 2 * l : ℕ) : k)) else 0 := ⟨_, fun _ => rfl⟩
  have key : ∀ l ∈ range (j + 1), c l = W l - W (l + 1) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rcases Nat.eq_or_lt_of_le hl' with hlj | hlj
    · have hne : (((l : ℕ) : k) * ((N - 2 * l : ℕ) : k)) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
      rw [hW, hW, ← hlj, if_pos le_rfl, if_neg (by omega), sub_zero, show N - l - l = N - 2 * l by omega,
        mul_div_assoc, div_self hne, mul_one]
    · obtain ⟨u, hu⟩ : ∃ u, j = l + 1 + u := ⟨j - l - 1, by omega⟩
      obtain ⟨v, hv⟩ : ∃ v, N = 2 * j + 1 + v := ⟨N - 2 * j - 1, by omega⟩
      rw [hW, hW, if_pos hl', if_pos (by omega), hc, hc]
      rw [show N - l - j = u + 2 + v by omega, show N - 2 * l - 1 = u + 1 + v + (u + 1) by omega,
        show N - 2 * l = 2 * u + 3 + v by omega, show N - l = 2 * u + 3 + v + l by omega,
        show j - l = u + 1 by omega,
        show N - (l + 1) - j = u + 1 + v by omega, show N - 2 * (l + 1) - 1 = u + v + u by omega,
        show N - 2 * (l + 1) = 2 * u + 1 + v by omega, show N - (l + 1) = 2 * u + 1 + v + (l + 1) by omega,
        show j - (l + 1) = u by omega]
      rw [cast_choose_add_eq_factorial_div_of_charZero (u + 1 + v) (u + 1), cast_choose_add_eq_factorial_div_of_charZero (2 * u + 3 + v) l,
        cast_choose_add_eq_factorial_div_of_charZero (u + v) u, cast_choose_add_eq_factorial_div_of_charZero (2 * u + 1 + v) (l + 1), hu]
      have F1 : ((u + 1).factorial : k) = ((u + 1 : ℕ) : k) * (u.factorial : k) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have F2 : ((u + 1 + v).factorial : k) = ((u + 1 + v : ℕ) : k) * ((u + v).factorial : k) := by
        rw [show u + 1 + v = u + v + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      have F3 : ((u + 1 + v + (u + 1)).factorial : k) =
          ((u + v + u + 2 : ℕ) : k) * ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show u + 1 + v + (u + 1) = u + v + u + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      have F4 : ((2 * u + 3 + v + l).factorial : k) =
          ((2 * u + 3 + v + l : ℕ) : k) * ((2 * u + 1 + v + (l + 1)).factorial : k) := by
        rw [show 2 * u + 3 + v + l = 2 * u + 1 + v + (l + 1) + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      have F5 : ((2 * u + 3 + v).factorial : k) = ((u + v + u + 3 : ℕ) : k) * ((u + v + u + 2 : ℕ) : k) *
          ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show 2 * u + 3 + v = u + v + u + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
          Nat.factorial_succ]
        push_cast
        ring
      have F6 : ((l + 1).factorial : k) = ((l + 1 : ℕ) : k) * (l.factorial : k) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have F7 : ((2 * u + 1 + v).factorial : k) = ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show 2 * u + 1 + v = u + v + u + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      rw [F3, F4, F5, F7, F2, F1, F6]
      clear hW hc W c hl hl' hlj hu hv hj hN F1 F2 F3 F4 F5 F6 F7
      have nB1 : ((u.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB1 : ((u.factorial : ℕ) : k) = B1 at nB1 ⊢
      have nB2 : (((u + v).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB2 : (((u + v).factorial : ℕ) : k) = B2 at nB2 ⊢
      have nB3 : (((u + v + u).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB3 : (((u + v + u).factorial : ℕ) : k) = B3 at nB3 ⊢
      have nB4 : ((l.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB4 : ((l.factorial : ℕ) : k) = B4 at nB4 ⊢
      have nB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) = B5 at nB5 ⊢
      have nL1 : ((u + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL1 : ((u + 1 : ℕ) : k) = L1 at nL1 ⊢
      have nL2 : ((u + 1 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL2 : ((u + 1 + v : ℕ) : k) = L2 at nL2 ⊢
      have nL3 : ((u + v + u + 2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL3 : ((u + v + u + 2 : ℕ) : k) = L3 at nL3 ⊢
      have nL4 : ((u + v + u + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL4 : ((u + v + u + 1 : ℕ) : k) = L4 at nL4 ⊢
      have nL5 : ((2 * u + 3 + v + l : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL5 : ((2 * u + 3 + v + l : ℕ) : k) = L5 at nL5 ⊢
      have nL6 : ((u + v + u + 3 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL6 : ((u + v + u + 3 : ℕ) : k) = L6 at nL6 ⊢
      have nL7 : ((l + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL7 : ((l + 1 : ℕ) : k) = L7 at nL7 ⊢
      have nL8 : ((l + 1 + u : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL8 : ((l + 1 + u : ℕ) : k) = L8 at nL8 ⊢
      have nL9 : ((2 * u + 3 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL9 : ((2 * u + 3 + v : ℕ) : k) = liftZP_newton at nL9 ⊢
      have nL10 : ((2 * u + 1 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL10 : ((2 * u + 1 + v : ℕ) : k) = ParameterUpperBound at nL10 ⊢
      field_simp [nB1, nB2, nB3, nB4, nB5, nL1, nL2, nL3, nL4, nL5, nL6, nL7, nL8, nL9, nL10]
      subst hB1 hB2 hB3 hB4 hB5 hL1 hL2 hL3 hL4 hL5 hL6 hL7 hL8 hL9 hL10
      push_cast
      ring
  simp only [← hc]
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub', hW, hW, if_pos (Nat.zero_le _), if_neg (by omega)]
  simp

theorem decomp [CharZero k] (hr : 1 ≤ r) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k)
    (hv : ∀ m, min o n < m → (tieF w e ^ m) x = 0) :
    X zv ^ z * x = ∑ l ∈ range (min o n + 1), ehP w e zv sv ^ l *
      M.tieP w e zv sv (o - l) (n - l) z
        (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) := by
  classical
  have hT : ∀ l m : ℕ, (tieF w e ^ m) ((tieF w e ^ l) x) = (tieF w e ^ (l + m)) x := by
    intro l m
    rw [add_comm, pow_add]
    rfl
  have hterm : ∀ l ∈ range (min o n + 1), ehP w e zv sv ^ l *
      M.tieP w e zv sv (o - l) (n - l) z
        (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) =
      ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (m) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (l + m) * (X zv ^ z * (tieF w e ^ (l + m)) x)) := by
    intro l hl
    have hlL : l ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hsub : range (min o n - l + 1) ⊆ range (o - l + 1) := by
      intro m hm
      simp only [Finset.mem_range] at hm ⊢
      omega
    rw [harmonicProjection_expand w e zv sv hz, Finset.mul_sum, ← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [LinearMap.map_smul, hT]
      simp only [MvPolynomial.smul_eq_C_mul, map_mul]
      ring
    · intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      have h0 : (tieF w e ^ (l + m)) x = 0 := hv (l + m) (by omega)
      simp [LinearMap.map_smul, hT, h0]
  have hre : ∀ l ∈ range (min o n + 1),
      ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (m) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (l + m) * (X zv ^ z * (tieF w e ^ (l + m)) x)) =
      ∑ j ∈ Ico l (min o n + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) := by
    intro l hl
    have hlL : l ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [Finset.sum_Ico_eq_sum_range, show min o n + 1 - l = min o n - l + 1 by omega]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left]
  have hcomm : ∑ l ∈ range (min o n + 1), ∑ j ∈ Ico l (min o n + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) =
      ∑ j ∈ range (min o n + 1), ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) :=
    Finset.sum_comm' (fun l j => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)
  have hid : ∀ j ∈ range (min o n + 1),
      ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) = if j = 0 then X zv ^ z * x else 0 := by
    intro j hj
    have hjL : j ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← Finset.sum_smul]
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      simp
    · rw [if_neg (by omega)]
      have hc2 : ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) = 0 := by
        refine Eq.trans ?_ (factorial_choose_signed_sum_eq_zero (o + n + r + z) j hpos (by omega))
        refine Finset.sum_congr rfl fun l hl => ?_
        have hlj : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        rw [show o - l + (n - l) + r + z - 1 = o + n + r + z - 2 * l - 1 by omega]
      rw [hc2, zero_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_congr rfl hre, hcomm, Finset.sum_congr rfl hid]
  simp

end

end Formalism.InvariantFactorPaths.KP.LL
