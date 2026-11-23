import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LogVandermondeBounds.LogVandermondeProofs.GammaIntegralPolynomialBound

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

theorem first_zeta_arithmetic_bound : ZetaValueArithmetic := by
  intro C₀ hC
  refine ⟨8 * C₀ + 11, ?_⟩
  intro ι _ N N' m n logHook logOm v L logT logg logK logh logh' lev logBlock logThn logS2 logTh
    hf hN hNN hm hv hL hT hg hlf hlN hlv hmax hK hh hh' hlev hBlock hThn hS2
  have hf1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hf
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNN' : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hNN
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsum : ∑ τ, ((N : ℝ) * N') * Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((N : ℝ) * N')))
      ≤ (Fintype.card ι : ℝ) * ((N : ℝ) * N') * (2 + C₀ * L) := by
    calc _ ≤ ∑ _τ : ι, ((N : ℝ) * N') * (2 + C₀ * L) := by
          apply sum_le_sum
          intro τ _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hmx : 0 < max 1 ((n τ : ℝ) / ((N : ℝ) * N')) := lt_of_lt_of_le one_pos (le_max_left _ _)
          rw [Real.log_mul (by positivity) hmx.ne', Real.log_mul (by norm_num) (Real.exp_pos 1).ne',
            Real.log_exp]
          have := Real.log_two_lt_d9
          linarith [hmax τ]
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
  generalize (∑ τ, ((N : ℝ) * N') * Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((N : ℝ) * N')))) = J
    at hsum hThn
  generalize (∑ τ, (logHook τ - n τ * logOm τ)) = Sg at hBlock ⊢
  generalize (Fintype.card ι : ℝ) = f at *
  generalize (N : ℝ) = Nr at *
  generalize (N' : ℝ) = Nr' at *
  generalize (m : ℝ) = mr at *
  have hN'1 : 1 ≤ Nr' := hN1.trans hNN'
  have hf0 : 0 < f := by linarith
  have hN0 : 0 < Nr := by linarith
  have hN'0 : 0 < Nr' := by linarith
  have hv0 : 0 < v := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hlN0 : Real.log Nr ≤ L := (Real.log_le_log hN0 hNN').trans hlN
  have hl2 := Real.log_two_lt_d9
  have hl4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl16 : Real.log 16 ≤ 3 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
  have hx1 : 1 ≤ f * Nr * Nr' * v := by
    have h1 : 1 ≤ f * Nr := one_le_mul_of_one_le_of_one_le hf1 hN1
    have h2 : 1 ≤ f * Nr * Nr' := one_le_mul_of_one_le_of_one_le h1 hN'1
    exact one_le_mul_of_one_le_of_one_le h2 hv
  have hbig : Real.log (2 + 8 * (f * Nr * Nr') * v) ≤ 3 + 4 * L := by
    calc Real.log (2 + 8 * (f * Nr * Nr') * v) ≤ Real.log (16 * (f * Nr * Nr' * v)) := by
          apply Real.log_le_log (by positivity); linarith
      _ = Real.log 16 + (Real.log f + Real.log Nr + Real.log Nr' + Real.log v) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) hv0.ne',
            Real.log_mul (by positivity) hN'0.ne', Real.log_mul hf0.ne' hN0.ne']
      _ ≤ 3 + 4 * L := by linarith
  have hfN : Real.log (f * Nr') ≤ 2 * L := by
    rw [Real.log_mul hf0.ne' hN'0.ne']; linarith
  have hE0 : 0 ≤ L + logT + logg := by linarith
  have hm2 : 1 ≤ mr ^ 2 := one_le_pow₀ hm1
  have hP0 : 0 ≤ f * mr ^ 2 * Nr' ^ 2 := by positivity
  have a1 : f * Nr' ^ 2 ≤ f * mr ^ 2 * Nr' ^ 2 := by
    have : f * Nr' ^ 2 * 1 ≤ f * Nr' ^ 2 * mr ^ 2 := by gcongr
    linarith
  have a2 : f * Nr * Nr' ≤ f * Nr' ^ 2 := by
    have : f * Nr * Nr' ≤ f * Nr' * Nr' := by gcongr
    linarith [this, sq Nr']
  have a3 : f * Nr' ≤ f * Nr' ^ 2 := by
    have : f * Nr' * 1 ≤ f * Nr' * Nr' := by gcongr
    nlinarith [this]
  have a4 : f * (mr ^ 2 * Nr + Nr * Nr') ≤ 2 * (f * mr ^ 2 * Nr' ^ 2) := by
    have h1 : f * (mr ^ 2 * Nr) ≤ f * (mr ^ 2 * Nr' ^ 2) := by
      have : Nr ≤ Nr' ^ 2 := by nlinarith
      gcongr
    have h2 : f * (Nr * Nr') ≤ f * mr ^ 2 * Nr' ^ 2 := by linarith
    linarith
  have t1 : f * Nr' ^ 2 * (L + logT + logg) ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul_of_nonneg_right a1 hE0
  have t2 : f * Nr' * L ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a3.trans a1) (by linarith) hL0 hP0
  have t3 : f * Nr' * logT ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a3.trans a1) (by linarith) hT hP0
  have t4 : f * (mr ^ 2 * Nr + Nr * Nr') * logg
      ≤ 2 * (f * mr ^ 2 * Nr' ^ 2) * (L + logT + logg) :=
    mul_le_mul a4 (by linarith) hg (by positivity)
  have t5 : f * Nr * Nr' * L ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a2.trans a1) (by linarith) hL0 hP0
  have t6 : f * Nr * Nr' * 1 ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a2.trans a1) (by linarith) zero_le_one hP0
  have c1 := mul_le_mul_of_nonneg_left t1 hC
  have c2 := mul_le_mul_of_nonneg_left t2 hC
  have c3 := mul_le_mul_of_nonneg_left t3 hC
  have c4 := mul_le_mul_of_nonneg_left t4 hC
  have c5 := mul_le_mul_of_nonneg_left t5 hC
  have e1 : C₀ * f * Nr' * Real.log (f * Nr') ≤ C₀ * f * Nr' * (2 * L) := by gcongr
  have e2 : (f * Nr * Nr') * Real.log 4 ≤ (f * Nr * Nr') * 2 := by gcongr
  have e3 : (f * Nr * Nr') * Real.log (2 + 8 * (f * Nr * Nr') * v) ≤ (f * Nr * Nr') * (3 + 4 * L) := by
    gcongr
  generalize Real.log (f * Nr') = z1 at *
  generalize Real.log 4 = z2 at *
  generalize Real.log (2 + 8 * (f * Nr * Nr') * v) = z3 at *
  linarith

private lemma log_weyl_dimension_bound (n : ℕ) (lam : Fin (n + 1) → ℤ) (h : Antitone lam) :
    Real.log (weylDim lam) ≤ ((n : ℝ) + 1) ^ 2 * Real.log (Wnum lam : ℝ) := by
  have hW1 : (1 : ℝ) ≤ (Wnum lam : ℝ) := by
    have h0 : lam (Fin.last n) ≤ lam 0 := h (Fin.zero_le _)
    have : (1 : ℤ) ≤ Wnum lam := by unfold Wnum; omega
    exact_mod_cast this
  have hfac : ∀ i j : Fin (n + 1), i < j →
      1 ≤ (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) ∧
      (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ≤ (Wnum lam : ℝ) := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have hd : (1 : ℝ) ≤ ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij'
      linarith
    have h1 : lam j ≤ lam i := h hij.le
    have h2 : lam i ≤ lam 0 := h (Fin.zero_le _)
    have h3 : lam (Fin.last n) ≤ lam j := h (Fin.le_last _)
    have hj : (j : ℕ) ≤ n := j.is_le
    have hnum : (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ))
        = ((lam i - lam j : ℤ) : ℝ) + (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by push_cast; ring
    have h1' : (0 : ℝ) ≤ ((lam i - lam j : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h1
    constructor
    · rw [le_div_iff₀ (by linarith), hnum]; linarith
    · rw [div_le_iff₀ (by linarith)]
      have h4 : (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ)) ≤ (Wnum lam : ℝ) := by
        have : lam i - lam j + (j : ℤ) - (i : ℤ) ≤ Wnum lam := by unfold Wnum; omega
        exact_mod_cast this
      nlinarith
  have hpos : 0 < weylDim lam := by
    unfold weylDim
    apply prod_pos; intro i _; apply prod_pos; intro j hj
    have := (hfac i j (by simpa using hj)).1
    linarith
  have hle : weylDim lam ≤ (Wnum lam : ℝ) ^ ((n + 1) * (n + 1)) := by
    unfold weylDim
    calc _ ≤ ∏ _i : Fin (n + 1), (Wnum lam : ℝ) ^ (n + 1) := by
          apply prod_le_prod
          · intro i _; apply prod_nonneg; intro j hj
            have := (hfac i j (by simpa using hj)).1
            linarith
          · intro i _
            calc _ ≤ ∏ _j ∈ univ.filter (fun j : Fin (n + 1) => i < j), (Wnum lam : ℝ) := by
                  apply prod_le_prod
                  · intro j hj
                    have := (hfac i j (by simpa using hj)).1
                    linarith
                  · intro j hj
                    exact (hfac i j (by simpa using hj)).2
              _ = (Wnum lam : ℝ) ^ (univ.filter (fun j : Fin (n + 1) => i < j)).card := by
                  rw [prod_const]
              _ ≤ (Wnum lam : ℝ) ^ (n + 1) := by
                  apply pow_le_pow_right₀ hW1
                  calc _ ≤ (univ : Finset (Fin (n + 1))).card := card_filter_le _ _
                    _ = n + 1 := by simp
      _ = _ := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]
  calc Real.log (weylDim lam) ≤ Real.log ((Wnum lam : ℝ) ^ ((n + 1) * (n + 1))) :=
        Real.log_le_log hpos hle
    _ = (((n + 1) * (n + 1) : ℕ) : ℝ) * Real.log (Wnum lam : ℝ) := Real.log_pow _ _
    _ = _ := by push_cast; ring

private lemma arithmetic_bound_at_top {C₀ L logT b' eta S mt nn d M lw ld B bt A : ℝ} (hC : 0 ≤ C₀) (hL : 0 ≤ L)
    (hT : 0 ≤ logT) (hb : 0 ≤ b') (he : 0 ≤ eta) (hS : 0 ≤ S) (hmt : 0 ≤ mt) (hn : 0 ≤ nn)
    (hM0 : 0 ≤ M) (hM : M ≤ 3 * B + (eta + S)) (hlw : lw ≤ C₀ * L) (hld : ld ≤ (nn + 1) ^ 2 * lw)
    (hbt : bt ≤ 2 * b') (hB : B ≤ bt + eta + S) (hd : A - bt - C₀ * (S + eta + mt) ≤ d) :
    -d * logT + 2 * nn * lw * M + ld ≤ -A * logT + (12 * C₀ + 2) * b' * (logT + (nn + 1) * L)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L) := by
  have h1 : -d * logT ≤ (-A + 2 * b' + C₀ * (S + eta + mt)) * logT :=
    mul_le_mul_of_nonneg_right (by linarith) hT
  have h2 : 2 * nn * lw * M ≤ 2 * nn * (C₀ * L) * M := by gcongr
  have h3 : 2 * nn * (C₀ * L) * M ≤ 2 * nn * (C₀ * L) * (6 * b' + 4 * eta + 4 * S) := by
    gcongr; linarith
  have h4 : ld ≤ (nn + 1) ^ 2 * (C₀ * L) := hld.trans (by gcongr)
  have key : 0 ≤ (-A * logT + (12 * C₀ + 2) * b' * (logT + (nn + 1) * L)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L))
      - ((-A + 2 * b' + C₀ * (S + eta + mt)) * logT
        + 2 * nn * (C₀ * L) * (6 * b' + 4 * eta + 4 * S) + (nn + 1) ^ 2 * (C₀ * L)) := by
    ring_nf; positivity
  linarith

private lemma arithmetic_bound_off_top {C₀ L logT eta S mt nn d M lw ld B : ℝ} (hC : 0 ≤ C₀) (hL : 0 ≤ L)
    (hT : 0 ≤ logT) (he : 0 ≤ eta) (hS : 0 ≤ S) (hmt : 0 ≤ mt) (hn : 0 ≤ nn)
    (hM0 : 0 ≤ M) (hM : M ≤ 3 * B + (eta + S)) (hlw : lw ≤ C₀ * L) (hld : ld ≤ (nn + 1) ^ 2 * lw)
    (hB : B ≤ eta + S) (hd : -(S + eta) - C₀ * mt ≤ d) :
    -d * logT + 2 * nn * lw * M + ld ≤ 0
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L) := by
  have h1 : -d * logT ≤ (S + eta + C₀ * mt) * logT :=
    mul_le_mul_of_nonneg_right (by linarith) hT
  have h2 : 2 * nn * lw * M ≤ 2 * nn * (C₀ * L) * M := by gcongr
  have h3 : 2 * nn * (C₀ * L) * M ≤ 2 * nn * (C₀ * L) * (4 * eta + 4 * S) := by
    gcongr; linarith
  have h4 : ld ≤ (nn + 1) ^ 2 * (C₀ * L) := hld.trans (by gcongr)
  have key : 0 ≤ (0 + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L))
      - ((S + eta + C₀ * mt) * logT
        + 2 * nn * (C₀ * L) * (4 * eta + 4 * S) + (nn + 1) ^ 2 * (C₀ * L)) := by
    ring_nf; positivity
  linarith

theorem third_zeta_application : ZetaBoundApplication := by
  intro C₀ hC
  refine ⟨12 * C₀ + 2, ?_⟩
  intro ι _ _ TT n lam sg A bt b' L logT eta S mt logP hL hT hb he hS hmt hI hW hbt hBt hBn hX
    hdt hdn hP
  have hL0 : 0 ≤ L := by linarith
  have hplace : ∀ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT ≤
      (if ρ ∈ TT then -A ρ * logT + (12 * C₀ + 2) * b' * (logT + ((n : ℝ) + 1) * L) else 0)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + (12 * C₀ + 2) * ((n : ℝ) + 1) ^ 2 * L) := by
    intro ρ
    obtain ⟨X, hXc, hXs⟩ := hX ρ
    have hB0 : 0 ≤ B0 (lam ρ) (sg ρ) := sum_nonneg (fun i _ => sub_nonneg.mpr ((hI ρ).2 i).1)
    have hlen : ∀ i, 0 ≤ len (lam ρ) i :=
      fun i => sub_nonneg.mpr (((hI ρ).2 i).1.trans ((hI ρ).2 i).2)
    have hM0 : 0 ≤ ∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) :=
      sum_nonneg fun i _ => le_min (hlen i) hB0
    have hM : ∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ))
        ≤ 3 * B0 (lam ρ) (sg ρ) + ∑ i ∈ Xᶜ, len (lam ρ) i := by
      rw [← Finset.sum_add_sum_compl X]
      refine add_le_add ?_ (Finset.sum_le_sum fun i _ => min_le_left _ _)
      calc ∑ i ∈ X, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) ≤ ∑ _i ∈ X, B0 (lam ρ) (sg ρ) :=
            Finset.sum_le_sum fun i _ => min_le_right _ _
        _ = X.card * B0 (lam ρ) (sg ρ) := by simp
        _ ≤ 3 * B0 (lam ρ) (sg ρ) := by
            apply mul_le_mul_of_nonneg_right _ hB0
            exact_mod_cast hXc
    have hcast : (∑ i, ((min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ))
        = ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ) := (Int.cast_sum _ _).symm
    have hM0r : (0 : ℝ) ≤ ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ) := by
      exact_mod_cast hM0
    have hMr : ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ)
        ≤ 3 * (B0 (lam ρ) (sg ρ) : ℝ) + (eta + S) := by
      have : ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ)
          ≤ ((3 * B0 (lam ρ) (sg ρ) + ∑ i ∈ Xᶜ, len (lam ρ) i : ℤ) : ℝ) := by exact_mod_cast hM
      rw [Int.cast_add, Int.cast_mul] at this
      have h3 : ((3 : ℤ) : ℝ) = 3 := by norm_num
      rw [h3] at this
      linarith
    have hdim := log_weyl_dimension_bound n (lam ρ) (hI ρ).1
    unfold MeanSquareTwistBound
    rw [hcast]
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      exact arithmetic_bound_at_top hC hL0 hT hb he hS hmt (Nat.cast_nonneg n) hM0r hMr (hW ρ) hdim (hbt ρ hρ)
        (hBt ρ hρ) (hdt ρ hρ)
    · rw [if_neg hρ]
      exact arithmetic_bound_off_top hC hL0 hT he hS hmt (Nat.cast_nonneg n) hM0r hMr (hW ρ) hdim
        (hBn ρ hρ) (hdn ρ hρ)
  calc logP ≤ ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT := hP
    _ ≤ ∑ ρ, ((if ρ ∈ TT then -A ρ * logT + (12 * C₀ + 2) * b' * (logT + ((n : ℝ) + 1) * L) else 0)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + (12 * C₀ + 2) * ((n : ℝ) + 1) ^ 2 * L)) := sum_le_sum fun ρ _ => hplace ρ
    _ = _ := by
      rw [sum_add_distrib, sum_const, sum_ite_mem, univ_inter, sum_add_distrib, sum_const,
        ← sum_mul, sum_neg_distrib, card_univ, nsmul_eq_mul, nsmul_eq_mul]
      ring

private lemma stirling_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have h1 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have h2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

private lemma stirling_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    have key : Real.log ((n : ℝ) / (n + 1)) ≤ (n : ℝ) / (n + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at key
    have e : (n : ℝ) / (n + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by field_simp; ring
    rw [e] at key
    have k2 : ((n : ℝ) + 1) * (Real.log n - Real.log ((n : ℝ) + 1)) ≤ -1 := by
      have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      have e2 : ((n : ℝ) + 1) * -(1 / ((n : ℝ) + 1)) = -1 := by field_simp
      linarith
    nlinarith

private lemma log_factorial_row_bound (n : ℕ) (x : ℝ) (hx : 1 ≤ x) (h : (n : ℝ) ≤ x) :
    Real.log (n.factorial : ℝ) ≤ x * Real.log x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using mul_nonneg (by linarith) (Real.log_nonneg hx)
  have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h2 : Real.log (n : ℝ) ≤ Real.log x := Real.log_le_log (by exact_mod_cast hn) h
  have h3 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log (by positivity) h1
    _ = n * Real.log n := Real.log_pow _ _
    _ ≤ x * Real.log x := mul_le_mul h h2 h3 (by linarith)

private lemma sum_log_factorial_rows_bounds (k : ℕ) (g : Fin k → ℕ) (x : ℝ) (hx : 1 ≤ x) (h : ∀ i, (g i : ℝ) ≤ x) :
    0 ≤ ∑ i, Real.log ((g i).factorial : ℝ) ∧
      ∑ i, Real.log ((g i).factorial : ℝ) ≤ k * (x * Real.log x) := by
  constructor
  · exact Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast Nat.factorial_pos _)
  · calc ∑ i, Real.log ((g i).factorial : ℝ) ≤ ∑ _i : Fin k, x * Real.log x :=
          Finset.sum_le_sum fun i _ => log_factorial_row_bound _ _ hx (h i)
      _ = k * (x * Real.log x) := by simp

private lemma log_factorial_shift_bound (n k : ℕ) (x : ℝ) (h : ((n + k : ℕ) : ℝ) ≤ x) :
    Real.log ((n + k).factorial : ℝ) ≤ Real.log (n.factorial : ℝ) + k * Real.log x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h' : ((n + k : ℕ) : ℝ) ≤ x := by push_cast at h ⊢; linarith
    have h1 := ih h'
    rw [← add_assoc, Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    have h2 : Real.log ((n : ℝ) + k + 1) ≤ Real.log x :=
      Real.log_le_log (by positivity) (by push_cast at h; linarith)
    nlinarith

private lemma log_hook_product_bounds (R : ℕ) (nu : Fin (R + 1) → ℕ) (h : Antitone nu) :
    Real.log (hookF nu) ≤ ∑ i : Fin (R + 1), Real.log ((nu i + R - i : ℕ).factorial : ℝ) ∧
    ∑ i : Fin (R + 1), Real.log ((nu i + R - i : ℕ).factorial : ℝ)
        - ((R : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + R + 1) ≤ Real.log (hookF nu) := by
  obtain ⟨h1, h2, -⟩ := Formalism.LogVandermondeBounds.flipTwoThree.hook_product_bounds R nu h
  refine ⟨?_, h2⟩
  have hpos : 0 < hookF nu := by
    unfold Formalism.LogVandermondeBounds.flipTwoThree.hookF
    apply div_pos (by positivity)
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    linarith [(Formalism.LogVandermondeBounds.flipTwoThree.hook_den_bounds R nu h i j (mem_filter.mp hj).2).1]
  calc Real.log (hookF nu) ≤ Real.log (∏ i : Fin (R + 1), ((nu i + R - i : ℕ).factorial : ℝ)) :=
        Real.log_le_log hpos h1
    _ = _ := Real.log_prod (fun i _ => by positivity)

private lemma sum_rows_bounds (k : ℕ) (g : Fin k → ℕ) (x : ℝ) (h : ∀ i, (g i : ℝ) ≤ x) :
    0 ≤ ∑ i, (g i : ℝ) ∧ ∑ i, (g i : ℝ) ≤ k * x := by
  constructor
  · exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  · calc ∑ i, (g i : ℝ) ≤ ∑ _i : Fin k, x := Finset.sum_le_sum fun i _ => h i
      _ = k * x := by simp

set_option maxHeartbeats 800000 in
theorem second_zeta_top_bound : LargestPlaceHookBound := by
  intro C₀ hC
  refine ⟨21 + (3 + C₀) ^ 2 + C₀ * (2 + C₀), ?_⟩
  intro R nu A w a b' L logOm hnu h0 hw hrow haA hA2 hb1 hba hL hla hRb hOm
  have ha1 : (1 : ℝ) ≤ a := hb1.trans hba
  have hA1r : (1 : ℝ) ≤ A := ha1.trans haA
  have hA1 : 1 ≤ A := by exact_mod_cast hA1r
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  set l5 := Real.log (5 * a) with hl5def
  have hl5 : l5 ≤ 5 * L := by
    rw [hl5def, Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 5 ≤ 5 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hl50 : 0 ≤ l5 := Real.log_nonneg (by linarith)
  set X := (3 + C₀) * b' with hX
  have hX1 : 1 ≤ X := by nlinarith
  have hlX : Real.log X ≤ (3 + C₀) * L := by
    rw [hX, Real.log_mul (by linarith) (by linarith)]
    have h1 : Real.log (3 + C₀) ≤ (3 + C₀) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : Real.log b' ≤ Real.log a := Real.log_le_log (by linarith) hba
    nlinarith
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  obtain ⟨hup, hlo⟩ := log_hook_product_bounds R nu hnu
  rw [Fin.sum_univ_succ] at hup hlo
  have e0 : nu 0 + R - ((0 : Fin (R + 1)) : ℕ) = A + (w + R) := by
    have : ((0 : Fin (R + 1)) : ℕ) = 0 := rfl
    omega
  rw [e0] at hup hlo
  obtain ⟨hT0, hTU⟩ := sum_log_factorial_rows_bounds R (fun i : Fin R => nu i.succ + R - (i.succ : Fin (R + 1))) X hX1 (by
    intro i
    have h1 : ((nu i.succ + R - (i.succ : Fin (R + 1)) : ℕ) : ℝ) ≤ ((nu i.succ + R : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.sub_le _ _)
    have h2 := hrow i.succ (Fin.succ_ne_zero i)
    push_cast at h1
    rw [hX]
    linarith)
  set Tl := ∑ i : Fin R, Real.log ((nu i.succ + R - (i.succ : Fin (R + 1)) : ℕ).factorial : ℝ) with hTl
  obtain ⟨hS0, hSU⟩ := sum_rows_bounds R (fun i : Fin R => nu i.succ) ((2 + C₀) * b')
    (fun i => hrow i.succ (Fin.succ_ne_zero i))
  have hsum : ∑ i, (nu i : ℝ) = (A : ℝ) + w + ∑ i : Fin R, (nu i.succ : ℝ) := by
    rw [Fin.sum_univ_succ, h0]; push_cast; ring
  set S := ∑ i : Fin R, (nu i.succ : ℝ) with hS
  have hsh := log_factorial_shift_bound A (w + R) (5 * a) (by push_cast; linarith)
  have hmono : Real.log (A.factorial : ℝ) ≤ Real.log ((A + (w + R)).factorial : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_add_right _ _))
  have hlo' := stirling_lower_bound A hA1
  have hhi' := stirling_upper_bound A hA1
  have hlA : Real.log (A : ℝ) ≤ l5 := Real.log_le_log (by linarith) (by linarith)
  have hl0 : Real.log ((nu 0 : ℝ) + R + 1) ≤ l5 := by
    apply Real.log_le_log (by positivity)
    rw [h0]; push_cast; linarith
  set Q := ((R : ℝ) + 1) * b' * L with hQ
  have hbL : b' * L ≤ Q := by
    have := mul_nonneg hR0 (mul_nonneg (by linarith : (0:ℝ) ≤ b') (by linarith : (0:ℝ) ≤ L))
    rw [hQ]; linarith
  have hLQ : L ≤ Q := (le_mul_of_one_le_left (by linarith) hb1).trans hbL
  have t1 : ((w + R : ℕ) : ℝ) * l5 ≤ 15 * Q := by
    have : ((w + R : ℕ) : ℝ) ≤ 3 * b' := by push_cast; linarith
    calc ((w + R : ℕ) : ℝ) * l5 ≤ (3 * b') * (5 * L) := mul_le_mul this hl5 hl50 (by linarith)
      _ = 15 * (b' * L) := by ring
      _ ≤ 15 * Q := by linarith
  have t2 : (R : ℝ) * (X * Real.log X) ≤ (3 + C₀) ^ 2 * Q := by
    have h1 : X * Real.log X ≤ X * ((3 + C₀) * L) := mul_le_mul_of_nonneg_left hlX (by linarith)
    have h2 : (R : ℝ) * (X * Real.log X) ≤ ((R : ℝ) + 1) * (X * ((3 + C₀) * L)) :=
      mul_le_mul (by linarith) h1 (mul_nonneg (by linarith) hlX0) (by linarith)
    calc _ ≤ _ := h2
      _ = (3 + C₀) ^ 2 * Q := by rw [hX, hQ]; ring
  have t3 : ((R : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + R + 1) ≤ 5 * Q := by
    have h1 : ((R : ℝ) + 1) ^ 2 ≤ ((R : ℝ) + 1) * b' := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hRb (by linarith)
    calc _ ≤ ((R : ℝ) + 1) ^ 2 * l5 := mul_le_mul_of_nonneg_left hl0 (by positivity)
      _ ≤ (((R : ℝ) + 1) * b') * (5 * L) := mul_le_mul h1 hl5 hl50 (mul_nonneg (by linarith) (by linarith))
      _ = 5 * Q := by rw [hQ]; ring
  have t4 : |((w : ℝ) + S) * logOm| ≤ C₀ * (2 + C₀) * Q := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (w : ℝ) + S)]
    have h1 : (w : ℝ) + S ≤ ((R : ℝ) + 1) * ((2 + C₀) * b') := by
      have := mul_nonneg hC (by linarith : (0:ℝ) ≤ b')
      linarith
    calc ((w : ℝ) + S) * |logOm| ≤ (((R : ℝ) + 1) * ((2 + C₀) * b')) * (C₀ * L) :=
          mul_le_mul h1 hOm (abs_nonneg _)
            (mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith)))
      _ = C₀ * (2 + C₀) * Q := by rw [hQ]; ring
  have hgoal : placeTerm nu logOm - topTerm A logOm
      = (Real.log (hookF nu) - ((A : ℝ) * Real.log A - A)) - ((w : ℝ) + S) * logOm := by
    unfold placeTerm topTerm; rw [hsum]; ring
  have hfin : (21 + (3 + C₀) ^ 2 + C₀ * (2 + C₀)) * ((R : ℝ) + 1) * b' * L
      = (21 + (3 + C₀) ^ 2 + C₀ * (2 + C₀)) * Q := by rw [hQ]; ring
  rw [hgoal, hfin]
  obtain ⟨t4a, t4b⟩ := abs_le.mp t4
  have hQ0 : 0 ≤ Q := by linarith
  have hsq : 0 ≤ (3 + C₀) ^ 2 * Q := by positivity
  rw [abs_le]
  constructor <;> linarith

theorem second_zeta_thin_bound : ThinPlaceHookBound := by
  intro C₀ hC
  refine ⟨(3 + C₀) ^ 2 + C₀ * (2 + C₀), ?_⟩
  intro R nu b' L logOm hnu hrow hb1 hL hlb hRb hOm
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  set X := (3 + C₀) * b' with hX
  have hX1 : 1 ≤ X := by nlinarith
  have hlX : Real.log X ≤ (3 + C₀) * L := by
    rw [hX, Real.log_mul (by linarith) (by linarith)]
    have h1 : Real.log (3 + C₀) ≤ (3 + C₀) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    nlinarith
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  obtain ⟨hup, hlo⟩ := log_hook_product_bounds R nu hnu
  obtain ⟨hT0, hTU⟩ := sum_log_factorial_rows_bounds (R + 1) (fun i : Fin (R + 1) => nu i + R - (i : ℕ)) X hX1 (by
    intro i
    have h1 : ((nu i + R - (i : ℕ) : ℕ) : ℝ) ≤ ((nu i + R : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.sub_le _ _)
    have h2 := hrow i
    push_cast at h1
    rw [hX]
    linarith)
  set Tl := ∑ i : Fin (R + 1), Real.log ((nu i + R - (i : ℕ) : ℕ).factorial : ℝ) with hTl
  obtain ⟨hS0, hSU⟩ := sum_rows_bounds (R + 1) nu ((2 + C₀) * b') hrow
  set S := ∑ i, (nu i : ℝ) with hS
  have hl0 : Real.log ((nu 0 : ℝ) + R + 1) ≤ Real.log X := by
    apply Real.log_le_log (by positivity)
    have := hrow 0
    rw [hX]; linarith
  set Q := ((R : ℝ) + 1) * b' * L with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have t2 : ((R + 1 : ℕ) : ℝ) * (X * Real.log X) ≤ (3 + C₀) ^ 2 * Q := by
    have h1 : X * Real.log X ≤ X * ((3 + C₀) * L) := mul_le_mul_of_nonneg_left hlX (by linarith)
    calc ((R + 1 : ℕ) : ℝ) * (X * Real.log X) ≤ ((R + 1 : ℕ) : ℝ) * (X * ((3 + C₀) * L)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = (3 + C₀) ^ 2 * Q := by rw [hX, hQ]; push_cast; ring
  have t3 : ((R : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + R + 1) ≤ (3 + C₀) * Q := by
    have h1 : ((R : ℝ) + 1) ^ 2 ≤ ((R : ℝ) + 1) * b' := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hRb (by linarith)
    calc _ ≤ ((R : ℝ) + 1) ^ 2 * Real.log X := mul_le_mul_of_nonneg_left hl0 (by positivity)
      _ ≤ (((R : ℝ) + 1) * b') * ((3 + C₀) * L) := mul_le_mul h1 hlX hlX0 (mul_nonneg (by linarith) (by linarith))
      _ = (3 + C₀) * Q := by rw [hQ]; ring
  have t4 : |S * logOm| ≤ C₀ * (2 + C₀) * Q := by
    rw [abs_mul, abs_of_nonneg hS0]
    calc S * |logOm| ≤ (((R + 1 : ℕ) : ℝ) * ((2 + C₀) * b')) * (C₀ * L) :=
          mul_le_mul hSU hOm (abs_nonneg _) (by positivity)
      _ = C₀ * (2 + C₀) * Q := by rw [hQ]; push_cast; ring
  have hfin : ((3 + C₀) ^ 2 + C₀ * (2 + C₀)) * ((R : ℝ) + 1) * b' * L
      = ((3 + C₀) ^ 2 + C₀ * (2 + C₀)) * Q := by rw [hQ]; ring
  unfold placeTerm
  rw [hfin]
  obtain ⟨t4a, t4b⟩ := abs_le.mp t4
  have h33 : (3 + C₀) * Q ≤ (3 + C₀) ^ 2 * Q := by
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 3 + C₀) (by linarith : (0:ℝ) ≤ 2 + C₀)) hQ0
    linarith
  rw [abs_le]
  constructor <;> linarith

private lemma mean_mono' {σ : Type} [Fintype σ] (F G : σ → ℝ) (h : ∀ s, F s ≤ G s) :
    mean F ≤ mean G := by
  unfold mean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => h s) (Nat.cast_nonneg _)

private lemma mean_add_eq {σ : Type} [Fintype σ] (F G : σ → ℝ) :
    mean (fun s => F s + G s) = mean F + mean G := by
  unfold mean; rw [Finset.sum_add_distrib, add_div]

private lemma mean_finset_sum_comm {σ J : Type} [Fintype σ] [Fintype J] (F : J → σ → ℝ) :
    mean (fun s => ∑ j, F j s) = ∑ j, mean (F j) := by
  unfold mean; rw [Finset.sum_comm, Finset.sum_div]

private lemma mean_const_eq {σ : Type} [Fintype σ] [Nonempty σ] (c : ℝ) :
    mean (fun _ : σ => c) = c := by
  unfold mean
  have hc : (Fintype.card σ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

private lemma mean_place_term_comm {σ : Type} [Fintype σ] [Nonempty σ] {N : ℕ} (nu : Fin N → ℕ)
    (x : σ → ℝ) : mean (fun s => placeTerm nu (x s)) = placeTerm nu (mean x) := by
  have hc : (Fintype.card σ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold placeTerm mean
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem second_zeta_mean_of_top_thin (ht : LargestPlaceHookBound) (hth : ThinPlaceHookBound) : MeanLogNormBound := by
  intro C₀ hC
  obtain ⟨Ct, hCt⟩ := ht C₀ hC
  obtain ⟨Cn, hCn⟩ := hth C₀ hC
  refine ⟨|Ct| + |Cn| + 2 * C₀, ?_⟩
  intro ι σ _ _ _ _ TT T2 R N m nu A w a b' L logT logg logOm logOms logTh logK hdis hRN hL hla hb1
    hba hNL hT0 hg0 hsqm hanti htop hthin hper hOm hTh hK
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hb0 : (0:ℝ) ≤ b' := by linarith
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  have hR0 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg _
  have hRN' : (R:ℝ) + 1 ≤ N := by exact_mod_cast hRN
  have hRb : (R:ℝ) + 1 ≤ b' := by nlinarith
  have hlb : Real.log b' ≤ L := le_trans (Real.log_le_log (by linarith) hba) hla
  set f : ℝ := (Fintype.card ι : ℝ) with hf
  have hf0 : 0 ≤ f := Nat.cast_nonneg _
  set G : ℝ := (N:ℝ) * b' * L with hG
  have hG0 : 0 ≤ G := by positivity
  have hRG : ((R:ℝ) + 1) * b' * L ≤ G := by rw [hG]; gcongr
  have hRG0 : 0 ≤ ((R:ℝ) + 1) * b' * L := by positivity
  have hplace : ∀ τ, placeTerm (nu τ) logOm ≤ (if τ ∈ TT then topTerm (A τ) logOm else 0)
      + (if τ ∈ T2 then placeTerm (nu τ) logOm else 0) + (|Ct| + |Cn|) * G := by
    intro τ
    have hg1 : 0 ≤ |Ct| * G := by positivity
    have hg2 : 0 ≤ |Cn| * G := by positivity
    by_cases h1 : τ ∈ TT
    · have h2 : τ ∉ T2 := Finset.disjoint_left.1 hdis h1
      rw [if_pos h1, if_neg h2]
      obtain ⟨p1, p2, p3, p4, p5⟩ := htop τ h1
      have := hCt R (nu τ) (A τ) (w τ) a b' L logOm (hanti τ) p3 p4 p5 p1 p2 hb1 hba hL hla hRb hOm
      have h3 := (abs_le.1 this).2
      have h4 : Ct * ((R:ℝ) + 1) * b' * L ≤ |Ct| * G := by
        calc Ct * ((R:ℝ) + 1) * b' * L = Ct * (((R:ℝ) + 1) * b' * L) := by ring
          _ ≤ |Ct| * G := by gcongr; exact le_abs_self _
      linarith
    · by_cases h2 : τ ∈ T2
      · rw [if_neg h1, if_pos h2]; linarith
      · rw [if_neg h1, if_neg h2]
        have := hCn R (nu τ) b' L logOm (hanti τ) (hthin τ h1 h2) hb1 hL hlb hRb hOm
        have h3 := (abs_le.1 this).2
        have h4 : Cn * ((R:ℝ) + 1) * b' * L ≤ |Cn| * G := by
          calc Cn * ((R:ℝ) + 1) * b' * L = Cn * (((R:ℝ) + 1) * b' * L) := by ring
            _ ≤ |Cn| * G := by gcongr; exact le_abs_self _
        linarith
  have hsum : ∑ τ, placeTerm (nu τ) logOm ≤ ∑ τ ∈ TT, topTerm (A τ) logOm
      + ∑ τ ∈ T2, placeTerm (nu τ) logOm + f * ((|Ct| + |Cn|) * G) := by
    calc ∑ τ, placeTerm (nu τ) logOm ≤ ∑ τ, ((if τ ∈ TT then topTerm (A τ) logOm else 0)
      + (if τ ∈ T2 then placeTerm (nu τ) logOm else 0) + (|Ct| + |Cn|) * G) :=
          Finset.sum_le_sum fun τ _ => hplace τ
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.univ_inter, Finset.univ_inter]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf]
  have hmean : mean logK ≤ ∑ τ, placeTerm (nu τ) logOm + mean logTh
      + C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) := by
    calc mean logK ≤ mean (fun s => (∑ τ, placeTerm (nu τ) (logOms τ s) + logTh s)
        + C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)) := mean_mono' _ _ hK
      _ = _ := by
        rw [mean_add_eq, mean_add_eq, mean_finset_sum_comm, mean_const_eq]
        simp only [mean_place_term_comm, hper]
  have e1 : mean logTh ≤ C₀ * f * G := by
    refine le_trans hTh ?_
    have : (N:ℝ) ^ 2 * L ≤ G := by
      rw [hG]
      have h1 : (N:ℝ) ^ 2 * L ≤ N * b' := by nlinarith
      have h2 : (N:ℝ) * b' ≤ N * b' * L := by nlinarith [mul_nonneg hN0 hb0]
      linarith
    calc C₀ * f * (N:ℝ) ^ 2 * L = C₀ * f * ((N:ℝ) ^ 2 * L) := by ring
      _ ≤ _ := by gcongr
  have e2 : C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ C₀ * f * G := by
    calc C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)
        = C₀ * f * ((m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)) := by ring
      _ ≤ _ := by gcongr
  have hfin : (|Ct| + |Cn| + 2 * C₀) * f * N * b' * L
      = f * ((|Ct| + |Cn|) * G) + C₀ * f * G + C₀ * f * G := by rw [hG]; ring
  rw [hfin]
  linarith

theorem second_zeta_mean_bound : MeanLogNormBound := second_zeta_mean_of_top_thin second_zeta_top_bound second_zeta_thin_bound

end Formalism.HermitianLattices.TraceIntegrality
