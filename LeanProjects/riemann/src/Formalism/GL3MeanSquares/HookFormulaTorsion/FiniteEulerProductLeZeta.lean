import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower
import Formalism.LogVandermondeBounds.LogVandermondeProofs.InertPrimeCountBound

namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset
open Formalism.LogVandermondeBounds.StandardLattice

theorem density_split_primes : SplitDensity := by
  intro F _ _ _ M β hM hβ
  classical
  set q := Fintype.card F with hq
  have hq0 : 0 < q := Fintype.card_pos
  have fib : ∀ x : Fin M → F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = β} =
      if x = 0 then 0 else q ^ (M - 1) := by
    intro x
    split_ifs with hx
    · subst hx
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨y, hy⟩ => hβ (by simpa using hy.symm)⟩
    · obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx (funext h)

      have key : ∀ t : F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = t} =
          Fintype.card {y : Fin M → F // ∑ i, x i * y i = 0} := by
        intro t
        apply Fintype.card_congr
        exact
          { toFun := fun y => ⟨y.1 - Pi.single j (t / x j), by
              have h := y.2
              change dotProduct x (y.1 - Pi.single j (t / x j)) = 0
              change dotProduct x y.1 = t at h
              rw [dotProduct_sub, dotProduct_single, h, mul_div_cancel₀ _ hj, sub_self]⟩
            invFun := fun y => ⟨y.1 + Pi.single j (t / x j), by
              have h := y.2
              change dotProduct x (y.1 + Pi.single j (t / x j)) = t
              change dotProduct x y.1 = 0 at h
              rw [dotProduct_add, dotProduct_single, h, mul_div_cancel₀ _ hj, zero_add]⟩
            left_inv := fun y => by ext; simp
            right_inv := fun y => by ext; simp }
      have hsum : ∑ t : F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = t} = q ^ M := by
        rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv _), Fintype.card_fun,
          Fintype.card_fin]
      rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_const, Finset.card_univ,
        smul_eq_mul] at hsum
      rw [key β]
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ, mul_comm (q ^ k)] at *
      exact Nat.eq_of_mul_eq_mul_left hq0 hsum
  have e : Fintype.card {p : (Fin M → F) × (Fin M → F) // ∑ i, p.1 i * p.2 i = β} =
      ∑ x : Fin M → F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = β} := by
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (x y : Fin M → F) => ∑ i, x i * y i = β)), Fintype.card_sigma]
  have hcnt : ∑ x : Fin M → F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = β} =
      (q ^ M - 1) * q ^ (M - 1) := by
    rw [Finset.sum_congr rfl (fun x _ => fib x), Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, smul_eq_mul, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [e, hcnt]
  have h1 : 1 ≤ q ^ M := Nat.one_le_pow _ _ hq0
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [h2, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_sub h1]
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  push_cast
  simp only [inv_pow]
  field_simp
  ring

theorem density_inert_primes : InertDensity := by
  intro L _ _ _ q M β hcard hM hβ hβq
  classical
  obtain ⟨p, hchar⟩ := CharP.exists L
  obtain ⟨n, hp, hLn⟩ := FiniteField.card L p
  haveI := Fact.mk hp
  have hdvd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hLn, hcard, sq]⟩
  obtain ⟨k, -, hqk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hq2 : 2 ≤ q := by
    have h1 : 1 < q ^ 2 := hcard ▸ Fintype.one_lt_card
    by_contra h
    push_neg at h
    have : q ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have frob_sub : ∀ x y : L, (x - y) ^ q = x ^ q - y ^ q := by
    intro x y
    rw [hqk, sub_pow_char_pow]
  have hpow : ∀ x : L, x ^ (q ^ 2) = x := by
    intro x
    rw [← hcard]
    exact FiniteField.pow_card x

  have hNq : ∀ a : L, (a ^ (q + 1)) ^ q = a ^ (q + 1) := by
    intro a
    rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, hpow, ← pow_succ']

  have hroots : ∀ (m : ℕ) (γ : L), 0 < m → (Finset.univ.filter (fun a : L => a ^ m = γ)).card ≤ m := by
    intro m γ hm
    calc (Finset.univ.filter (fun a : L => a ^ m = γ)).card
        ≤ (Polynomial.nthRoots m γ).toFinset.card := by
          apply Finset.card_le_card
          intro a ha
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hm]
          exact (Finset.mem_filter.1 ha).2
      _ ≤ Multiset.card (Polynomial.nthRoots m γ) := Multiset.toFinset_card_le _
      _ ≤ m := Polynomial.card_nthRoots m γ
  set Fqs := Finset.univ.filter (fun b : L => b ^ q = b ∧ b ≠ 0) with hFqs
  have hmaps : ∀ a ∈ Finset.univ.erase (0 : L), a ^ (q + 1) ∈ Fqs := by
    intro a ha
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hNq a, pow_ne_zero _ (Finset.ne_of_mem_erase ha)⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard] at hsum
  have hle : ∀ γ ∈ Fqs,
      ((Finset.univ.erase (0 : L)).filter (fun a => a ^ (q + 1) = γ)).card ≤ q + 1 := by
    intro γ _
    exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _)))
      (hroots (q + 1) γ (by omega))
  have hFqs : Fqs.card ≤ q - 1 := by
    refine le_trans (Finset.card_le_card ?_) (hroots (q - 1) 1 (by omega))
    intro b hb
    obtain ⟨-, hbq, hb0⟩ := Finset.mem_filter.1 hb
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, mul_right_cancel₀ hb0 ?_⟩
    rw [pow_sub_one_mul (by omega : q ≠ 0), one_mul, hbq]
  have hsq : (q - 1) * (q + 1) = q ^ 2 - 1 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have heq : ∑ γ ∈ Fqs, ((Finset.univ.erase (0 : L)).filter (fun a => a ^ (q + 1) = γ)).card =
      ∑ γ ∈ Fqs, (q + 1) := by
    apply le_antisymm (Finset.sum_le_sum hle)
    rw [Finset.sum_const, smul_eq_mul, ← hsum, ← hsq]
    exact Nat.mul_le_mul_right _ hFqs
  have hfib := (Finset.sum_eq_sum_iff_of_le hle).1 heq

  have hc : ∀ γ : L, γ ^ q = γ →
      ((Finset.univ.filter (fun a : L => a ^ (q + 1) = γ)).card : ℝ) = if γ = 0 then 1 else q + 1 := by
    intro γ hγ
    split_ifs with h0
    · subst h0
      have : Finset.univ.filter (fun a : L => a ^ (q + 1) = 0) = {0} := by
        ext a
        simp [pow_eq_zero_iff (by omega : q + 1 ≠ 0)]
      rw [this, Finset.card_singleton, Nat.cast_one]
    · have hmem : γ ∈ Fqs := Finset.mem_filter.2 ⟨Finset.mem_univ _, hγ, h0⟩
      have e : (Finset.univ.erase (0 : L)).filter (fun a => a ^ (q + 1) = γ) =
          Finset.univ.filter (fun a : L => a ^ (q + 1) = γ) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨fun ha => h0 ?_, h⟩
          rw [← h, ha, zero_pow (by omega)]
      rw [← e, hfib γ hmem]

  have hrec : ∀ (m : ℕ) (γ : L),
      Fintype.card {x : Fin (m + 1) → L // ∑ i, x i ^ (q + 1) = γ} =
        ∑ a : L, Fintype.card {y : Fin m → L // ∑ i, y i ^ (q + 1) = γ - a ^ (q + 1)} := by
    intro m γ
    rw [← Fintype.card_sigma]
    refine Fintype.card_congr (Equiv.trans ?_
      (Equiv.subtypeProdEquivSigmaSubtype (fun (a : L) (y : Fin m → L) =>
        ∑ i, y i ^ (q + 1) = γ - a ^ (q + 1))))
    exact
      { toFun := fun x => ⟨(x.1 0, Fin.tail x.1), by
          have h := x.2
          rw [Fin.sum_univ_succ] at h
          show ∑ i : Fin m, x.1 i.succ ^ (q + 1) = γ - x.1 0 ^ (q + 1)
          linear_combination h⟩
        invFun := fun y => ⟨(Fin.cons y.1.1 y.1.2 : Fin (m + 1) → L), by
          rw [Fin.sum_univ_succ, Fin.cons_zero]
          simp only [Fin.cons_succ]
          linear_combination y.2⟩
        left_inv := fun x => Subtype.ext (Fin.cons_self_tail x.1)
        right_inv := fun y => Subtype.ext (by simp) }
  have hmain : ∀ (m : ℕ) (γ : L), γ ^ q = γ →
      (q : ℝ) * (Fintype.card {x : Fin m → L // ∑ i, x i ^ (q + 1) = γ} : ℝ) =
        if γ = 0 then (q : ℝ) ^ (2 * m) + (-1) ^ m * ((q : ℝ) - 1) * (q : ℝ) ^ m
        else (q : ℝ) ^ (2 * m) - (-1) ^ m * (q : ℝ) ^ m := by
    intro m
    induction m with
    | zero =>
      intro γ _
      split_ifs with h0
      · subst h0
        simp
      · have : Fintype.card {x : Fin 0 → L // ∑ i, x i ^ (q + 1) = γ} = 0 := by
          rw [Fintype.card_eq_zero_iff]
          exact ⟨fun ⟨x, hx⟩ => h0 (by simpa using hx.symm)⟩
        rw [this]
        simp
    | succ m ih =>
      intro γ hγ
      have hterm : ∀ a : L, (q : ℝ) *
          (Fintype.card {y : Fin m → L // ∑ i, y i ^ (q + 1) = γ - a ^ (q + 1)} : ℝ) =
          ((q : ℝ) ^ (2 * m) - (-1) ^ m * (q : ℝ) ^ m) +
            (q : ℝ) * (-1) ^ m * (q : ℝ) ^ m * (if a ^ (q + 1) = γ then 1 else 0) := by
        intro a
        rw [ih _ (by rw [frob_sub, hγ, hNq])]
        by_cases h : a ^ (q + 1) = γ
        · rw [if_pos (by rw [h, sub_self]), if_pos h]
          ring
        · rw [if_neg (fun h' => h (sub_eq_zero.1 h').symm), if_neg h]
          ring
      rw [hrec, Nat.cast_sum, Finset.mul_sum, Finset.sum_congr rfl (fun a _ => hterm a),
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
        ← Finset.mul_sum, Finset.sum_boole, hc γ hγ]
      push_cast
      split_ifs <;> ring
  have h := hmain M β hβq
  rw [if_neg hβ] at h
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  have h2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [h2]
  have hS : (Fintype.card {x : Fin (j + 1) → L // ∑ i, x i ^ (q + 1) = β} : ℝ) =
      ((q : ℝ) ^ (2 * (j + 1)) - (-1) ^ (j + 1) * (q : ℝ) ^ (j + 1)) / q := by
    rw [← h]
    field_simp
  rw [hS]
  simp only [inv_pow]
  field_simp
  ring

theorem global_arithmetic_identity : GlobalArithmeticIdentity := by
  intro f M v Lv hM hv hL
  show ((((2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)) ^ f * ((2 * v) ^ f) ^ ((1 : ℝ) / 2 - M) / Lv)⁻¹ =
    (((M - 1).factorial : ℝ) * (v / Real.pi) ^ M) ^ f / Real.sqrt ((2 * v) ^ f) * Lv)
  have hd : (0 : ℝ) < (2 * v) ^ f := by positivity
  rw [Real.rpow_sub hd, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt ((2 * v) ^ f) := Real.sqrt_pos.2 hd
  have hfac : (0 : ℝ) < ((M - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpi := Real.pi_pos
  have key : ((2 * v) ^ f) ^ M = ((2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)) ^ f *
      (((M - 1).factorial : ℝ) * (v / Real.pi) ^ M) ^ f := by
    rw [← pow_mul, mul_comm f M, pow_mul, ← mul_pow]
    congr 1
    rw [div_pow]
    field_simp
    ring
  rw [key]
  have hA : (0 : ℝ) < (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ) := by positivity
  have hB : (0 : ℝ) < ((M - 1).factorial : ℝ) * (v / Real.pi) ^ M := by positivity
  generalize (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ) = A at hA ⊢
  generalize ((M - 1).factorial : ℝ) * (v / Real.pi) ^ M = B at hB ⊢
  have hAf : 0 < A ^ f := pow_pos hA f
  have hBf : 0 < B ^ f := pow_pos hB f
  field_simp

private noncomputable def invPowMonoidHom (M : ℕ) : ℕ →* ℝ where
  toFun n := ((n : ℝ)⁻¹) ^ M
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_inv, mul_pow]

private lemma summable_inv_pow_of_two_le (M : ℕ) (hM : 2 ≤ M) : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ M) := by
  refine (Real.summable_nat_pow_inv.2 (by omega : 1 < M)).congr fun n => ?_
  rw [inv_pow]

private lemma tsum_inv_pow_eq_zeta (M : ℕ) (hM : 2 ≤ M) : ∑' n : ℕ, ((n : ℝ)⁻¹) ^ M = zetaR M := by
  rw [(summable_inv_pow_of_two_le M hM).tsum_eq_zero_add, zetaR]
  have h0 : ((((0 : ℕ) : ℝ))⁻¹) ^ M = 0 := by
    simp [zero_pow (by omega : M ≠ 0)]
  rw [h0, zero_add]
  congr 1
  ext n
  push_cast
  rw [one_div, inv_pow]

private lemma finite_euler_product_le_zeta (M : ℕ) (hM : 2 ≤ M) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹ ≤ zetaR M := by
  classical
  have hM0 : M ≠ 0 := by omega
  let F : ℕ →*₀ ℝ :=
    { toFun := fun n => ((n : ℝ)⁻¹) ^ M
      map_zero' := by simp [hM0]
      map_one' := by simp
      map_mul' := fun a b => by push_cast; rw [mul_inv, mul_pow] }
  have hF : ∀ n, F n = ((n : ℝ)⁻¹) ^ M := fun n => rfl
  have hsum : Summable (fun n => ‖F n‖) :=
    (summable_inv_pow_of_two_le M hM).congr fun n => by rw [hF, Real.norm_of_nonneg (by positivity)]
  have ht := EulerProduct.eulerProduct_completely_multiplicative hsum
  have htsum : ∑' n, F n = zetaR M := by
    simp only [hF]
    exact tsum_inv_pow_eq_zeta M hM
  rw [htsum] at ht
  have hfac : ∀ p : ℕ, p.Prime → 1 ≤ (1 - F p)⁻¹ := by
    intro p hp
    rw [hF]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have h1 : 0 ≤ ((p : ℝ)⁻¹) ^ M := by positivity
    have h2 : ((p : ℝ)⁻¹) ^ M < 1 := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hp1) hM0
    rw [one_le_inv₀ (by linarith)]
    linarith
  change ∏ p ∈ S, (1 - F p)⁻¹ ≤ zetaR M
  refine ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨S.sup id + 1, fun n hn => ?_⟩)
  have hsub : S ⊆ n.primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow]
    refine ⟨?_, hS p hp⟩
    have := Finset.le_sup (f := id) hp
    simp only [id] at this
    omega
  rw [← Finset.prod_sdiff hsub]
  apply le_mul_of_one_le_left
  · exact Finset.prod_nonneg fun p hp => le_trans zero_le_one (hfac p (hS p hp))
  · exact Finset.prod_induction _ (fun x => 1 ≤ x)
      (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      fun p hp => hfac p (Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.1 hp).1)

private lemma abs_log_inv_one_sub_le (s y x : ℝ) (hs : s = 1 ∨ s = -1) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) :
    |Real.log ((1 - s * y)⁻¹)| ≤ -Real.log (1 - x) := by
  rcases hs with rfl | rfl
  · have h1 : 0 < 1 - y := by linarith
    have h2 : 0 < 1 - x := by linarith
    rw [one_mul, Real.log_inv, abs_neg, abs_of_nonpos (Real.log_nonpos h1.le (by linarith))]
    have := Real.log_le_log h2 (by linarith : 1 - x ≤ 1 - y)
    linarith
  · rw [Real.log_inv, abs_neg, neg_one_mul, sub_neg_eq_add,
      abs_of_nonneg (Real.log_nonneg (by linarith))]
    have a := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + y)
    have b := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - x)
    linarith

theorem log_l_value_bound : LogLValueFinitePlaces := by
  intro f M ι _ pr Nv s hM hpr hN hs hcard
  classical
  have hM0 : M ≠ 0 := by omega
  have hxp : ∀ p : ℕ, p.Prime → 0 ≤ ((p : ℝ)⁻¹) ^ M ∧ ((p : ℝ)⁻¹) ^ M < 1 := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact ⟨by positivity, pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hp1) hM0⟩
  have hpos : ∀ v, 0 < (pr v : ℝ) := fun v => by exact_mod_cast (hpr v).pos
  have hy0 : ∀ v, 0 ≤ ((Nv v)⁻¹) ^ M := fun v => by
    have := lt_of_lt_of_le (hpos v) (hN v)
    positivity
  have hyx : ∀ v, ((Nv v)⁻¹) ^ M ≤ (((pr v : ℕ) : ℝ)⁻¹) ^ M := fun v =>
    pow_le_pow_left₀ (inv_nonneg.2 (lt_of_lt_of_le (hpos v) (hN v)).le)
      (inv_anti₀ (hpos v) (hN v)) M
  have hfpos : ∀ v, 0 < 1 - s v * ((Nv v)⁻¹) ^ M := by
    intro v
    have h1 := (hxp _ (hpr v)).2
    have h2 := hyx v
    rcases hs v with h | h <;> rw [h] <;> nlinarith [hy0 v]
  set T := Finset.univ.image pr with hT
  have hTp : ∀ p ∈ T, p.Prime := by
    intro p hp
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
    exact hpr v
  have hlogp : ∀ p ∈ T, 0 ≤ -Real.log (1 - ((p : ℝ)⁻¹) ^ M) := by
    intro p hp
    have := hxp p (hTp p hp)
    have : Real.log (1 - ((p : ℝ)⁻¹) ^ M) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  rw [Real.log_prod (fun v _ => (inv_pos.2 (hfpos v)).ne')]
  calc |∑ v, Real.log ((1 - s v * ((Nv v)⁻¹) ^ M)⁻¹)|
      ≤ ∑ v, |Real.log ((1 - s v * ((Nv v)⁻¹) ^ M)⁻¹)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, -Real.log (1 - (((pr v : ℕ) : ℝ)⁻¹) ^ M) := Finset.sum_le_sum fun v _ =>
        abs_log_inv_one_sub_le (s v) _ _ (hs v) (hy0 v) (hyx v) (hxp _ (hpr v)).2
    _ = ∑ p ∈ T, ∑ v ∈ Finset.univ.filter (fun v => pr v = p),
          -Real.log (1 - (((pr v : ℕ) : ℝ)⁻¹) ^ M) :=
        (Finset.sum_fiberwise_of_maps_to (fun v _ => Finset.mem_image_of_mem pr (Finset.mem_univ v)) _).symm
    _ ≤ ∑ p ∈ T, (f : ℝ) * -Real.log (1 - ((p : ℝ)⁻¹) ^ M) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.sum_congr rfl (g := fun _ => -Real.log (1 - ((p : ℝ)⁻¹) ^ M))
          (fun v hv => by rw [(Finset.mem_filter.1 hv).2]), Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard p) (hlogp p hp)
    _ = (f : ℝ) * Real.log (∏ p ∈ T, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹) := by
        rw [← Finset.mul_sum, Real.log_prod (fun p hp => (inv_pos.2 (by
          linarith [(hxp p (hTp p hp)).2])).ne')]
        simp only [Real.log_inv]
    _ ≤ (f : ℝ) * Real.log (zetaR M) := by
        refine mul_le_mul_of_nonneg_left (Real.log_le_log (Finset.prod_pos fun p hp => inv_pos.2 (by
          linarith [(hxp p (hTp p hp)).2])) (finite_euler_product_le_zeta M hM T hTp)) (Nat.cast_nonneg f)

end Formalism.HermitianLattices.GenusMassVolumes
