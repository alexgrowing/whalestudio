import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumLogFactorialRowsBounds

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

private lemma mean_le_of_le_const {σ : Type} [Fintype σ] [Nonempty σ] (F : σ → ℝ) (B : ℝ)
    (h : ∀ s, F s ≤ B) : mean F ≤ B := by
  unfold mean
  have hc : (0:ℝ) < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc]
  calc ∑ s, F s ≤ ∑ _s : σ, B := Finset.sum_le_sum fun s _ => h s
    _ = B * (Fintype.card σ : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

private lemma mean_le_mean_of_le {σ : Type} [Fintype σ] (F G : σ → ℝ) (h : ∀ s, F s ≤ G s) :
    mean F ≤ mean G := by
  unfold mean
  gcongr with s
  exact h s

private lemma mean_add_distrib {σ : Type} [Fintype σ] (F G : σ → ℝ) :
    mean (fun s => F s + G s) = mean F + mean G := by
  simp only [mean]
  rw [Finset.sum_add_distrib, add_div]

private lemma mean_sum_comm {σ J : Type} [Fintype σ] [Fintype J] (F : J → σ → ℝ) :
    mean (fun s => ∑ j, F j s) = ∑ j, mean (F j) := by
  simp only [mean]
  rw [Finset.sum_comm, Finset.sum_div]

private lemma square_moment_arithmetic_bound (C₀ L logT logg b' : ℝ) (m N : ℕ) (hC : 0 ≤ C₀) (hL : 1 ≤ L) (hm : 1 ≤ m)
    (hT : logT ≤ C₀ * m * L) (hg : logg ≤ C₀ * L) (hb : (1 + 2 * C₀) * (m : ℝ) ^ 3 * N ≤ b') :
    (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ N * b' * L := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hCL : 0 ≤ C₀ * L := mul_nonneg hC hL0
  have e1 : C₀ * L ≤ C₀ * m * L := by nlinarith [mul_nonneg hCL (sub_nonneg.2 hm')]
  have e2 : L ≤ m * L := by nlinarith [mul_nonneg (sub_nonneg.2 hm') hL0]
  have h1 : L + logT + logg ≤ (1 + 2 * C₀) * m * L := by linarith
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  calc (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)
      ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * ((1 + 2 * C₀) * m * L) := by gcongr
    _ = ((1 + 2 * C₀) * (m : ℝ) ^ 3 * N) * (N * L) := by ring
    _ ≤ b' * (N * L) := mul_le_mul_of_nonneg_right hb (mul_nonneg hN0 hL0)
    _ = N * b' * L := by ring

private lemma first_part_arithmetic_bound (C₀ C2 C3 f tt M tr Nn b' L logT eta S : ℝ) (hC : 0 ≤ C₀) (hf0 : 0 ≤ f)
    (htt0 : 0 ≤ tt) (htt : tt ≤ f) (hm1 : 1 ≤ M) (hNn1 : 1 ≤ Nn) (hb1 : 1 ≤ b') (hL : 1 ≤ L)
    (hT0 : 0 ≤ logT) (hTle : logT ≤ C₀ * M * L) (he : 0 ≤ eta) (hS : 0 ≤ S) (hmt : 0 ≤ M * tr)
    (hsmall : S + eta + M * tr ≤ b') (hNL : Nn * L ≤ b') :
    C3 * tt * b' * (logT + Nn * L) + C3 * f * (eta + 3 * S + M * tr) * (logT + Nn * L)
      + C3 * f * Nn ^ 2 * L + M * (C2 * f * Nn * b' * L)
      ≤ (|C2| + |C3| * (4 * (C₀ + 1) + 1)) * f * M * Nn * b' * L := by
  have hM0 : (0:ℝ) ≤ M := by linarith
  have hN0 : (0:ℝ) ≤ Nn := by linarith
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hb0 : (0:ℝ) ≤ b' := by linarith
  have hQ : 0 ≤ M * Nn * L := mul_nonneg (mul_nonneg hM0 hN0) hL0
  have hX0 : 0 ≤ logT + Nn * L := by nlinarith
  have hX : logT + Nn * L ≤ (C₀ + 1) * (M * Nn * L) := by
    have h1 : C₀ * M * L ≤ C₀ * M * Nn * L := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC hM0) hL0) (sub_nonneg.2 hNn1)]
    have h2 : Nn * L ≤ M * Nn * L := by
      nlinarith [mul_nonneg (mul_nonneg hN0 hL0) (sub_nonneg.2 hm1)]
    nlinarith
  have hY0 : 0 ≤ eta + 3 * S + M * tr := by linarith
  have hY : eta + 3 * S + M * tr ≤ 3 * b' := by linarith
  have k1 : tt * b' * (logT + Nn * L) ≤ f * b' * ((C₀ + 1) * (M * Nn * L)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right htt hb0) hX hX0 (mul_nonneg hf0 hb0)
  have t1 : C3 * tt * b' * (logT + Nn * L) ≤ |C3| * (f * b' * ((C₀ + 1) * (M * Nn * L))) := by
    calc C3 * tt * b' * (logT + Nn * L) = C3 * (tt * b' * (logT + Nn * L)) := by ring
      _ ≤ |C3| * (tt * b' * (logT + Nn * L)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (mul_nonneg htt0 hb0) hX0)
      _ ≤ |C3| * (f * b' * ((C₀ + 1) * (M * Nn * L))) := mul_le_mul_of_nonneg_left k1 (abs_nonneg _)
  have k2 : f * (eta + 3 * S + M * tr) * (logT + Nn * L) ≤ f * (3 * b') * ((C₀ + 1) * (M * Nn * L)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hY hf0) hX hX0 (mul_nonneg hf0 (by linarith))
  have t2 : C3 * f * (eta + 3 * S + M * tr) * (logT + Nn * L)
      ≤ |C3| * (f * (3 * b') * ((C₀ + 1) * (M * Nn * L))) := by
    calc C3 * f * (eta + 3 * S + M * tr) * (logT + Nn * L)
        = C3 * (f * (eta + 3 * S + M * tr) * (logT + Nn * L)) := by ring
      _ ≤ |C3| * (f * (eta + 3 * S + M * tr) * (logT + Nn * L)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (mul_nonneg hf0 hY0) hX0)
      _ ≤ _ := mul_le_mul_of_nonneg_left k2 (abs_nonneg _)
  have hML : 1 ≤ M * L := by nlinarith
  have a1 : Nn ^ 2 * L ≤ Nn * b' := by
    calc Nn ^ 2 * L = Nn * (Nn * L) := by ring
      _ ≤ Nn * b' := mul_le_mul_of_nonneg_left hNL hN0
  have a2 : Nn * b' ≤ M * Nn * b' * L := by
    calc Nn * b' = Nn * b' * 1 := by ring
      _ ≤ Nn * b' * (M * L) := mul_le_mul_of_nonneg_left hML (mul_nonneg hN0 hb0)
      _ = M * Nn * b' * L := by ring
  have k3 : f * Nn ^ 2 * L ≤ f * (M * Nn * b' * L) := by
    calc f * Nn ^ 2 * L = f * (Nn ^ 2 * L) := by ring
      _ ≤ f * (M * Nn * b' * L) := mul_le_mul_of_nonneg_left (a1.trans a2) hf0
  have t3 : C3 * f * Nn ^ 2 * L ≤ |C3| * (f * (M * Nn * b' * L)) := by
    calc C3 * f * Nn ^ 2 * L = C3 * (f * Nn ^ 2 * L) := by ring
      _ ≤ |C3| * (f * Nn ^ 2 * L) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (mul_nonneg hf0 (sq_nonneg _)) hL0)
      _ ≤ _ := mul_le_mul_of_nonneg_left k3 (abs_nonneg _)
  have t4 : M * (C2 * f * Nn * b' * L) ≤ |C2| * (f * M * Nn * b' * L) := by
    calc M * (C2 * f * Nn * b' * L) = C2 * (f * M * Nn * b' * L) := by ring
      _ ≤ |C2| * (f * M * Nn * b' * L) :=
          mul_le_mul_of_nonneg_right (le_abs_self _)
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf0 hM0) hN0) hb0) hL0)
  linarith [t1, t2, t3, t4]

theorem PropZ_i_of (h2 : MeanLogNormBound) (h3 : ZetaBoundApplication) : PropZ_i := by
  intro C₀ hC
  obtain ⟨C2, hC2⟩ := h2 C₀ hC
  obtain ⟨C3, hC3⟩ := h3 C₀ hC
  refine ⟨|C2| + |C3| * (4 * (C₀ + 1) + 1), ?_⟩
  intro ι σ _ _ _ _ TT T2 k m t n R nu A w bt lam sg a b' L v logT logg eta S logOm logOms logTh
    logK logP logPK hN hdis hR hanti htop htopj hthin hper hOm hTh hK hI hW hB0t hB0o hX hdt hdo
    hP hPK
  have hL := hN.one_le_L
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hb1 := hN.one_le_b'
  have hb0 : (0:ℝ) ≤ b' := by linarith
  have hba := hN.b'_le_a
  have hT0 := hN.logT_nonneg
  have hg0 := hN.logg_nonneg
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hN.one_le_m
  have hm0 : (0:ℝ) ≤ m := by linarith
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hmt : (0:ℝ) ≤ (m:ℝ) * t := mul_nonneg hm0 ht0
  have ha0 : (0:ℝ) < a := by linarith
  have hloga : Real.log a ≤ L := by
    refine le_trans (Real.log_le_log ha0 ?_) hN.log_av
    nlinarith [hN.one_le_v]
  have hlin := hN.lin
  push_cast at hlin
  have hNL : ((n:ℝ) + 1) * L ≤ b' := by linarith
  have hsqm := square_moment_arithmetic_bound C₀ L logT logg b' m (n + 1) hC hL hN.one_le_m hN.logT_le hN.logg_le hN.pow
  have key2 : ∀ j, mean (logK j) ≤ ∑ τ ∈ TT, topTerm (A τ) logOm
      + ∑ τ ∈ T2, placeTerm (nu j τ) logOm + C2 * Fintype.card ι * ((n:ℝ) + 1) * b' * L := by
    intro j
    have := hC2 ι σ TT T2 (R j) (n + 1) m (nu j) A (w j) a b' L logT logg logOm logOms (logTh j)
      (logK j) hdis (hR j) hL hloga hb1 hba (by push_cast; exact hNL) hT0 hg0 hsqm (hanti j)
      (fun τ hτ => ⟨(htop τ hτ).1, (htop τ hτ).2.1, (htopj j τ hτ).1, (htopj j τ hτ).2.1,
        (htopj j τ hτ).2.2⟩)
      (hthin j) hper hOm (by push_cast; exact hTh j) (by push_cast; exact hK j)
    push_cast at this
    exact this
  have key3 := hC3 ι TT n lam sg (fun ρ => (A ρ : ℝ)) bt b' L logT eta S ((m:ℝ) * t)
    (∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT) hL hT0 hb0 hN.eta_nonneg hN.S_nonneg hmt hI hW
    (fun ρ h => (htop ρ h).2.2) hB0t hB0o hX hdt hdo le_rfl
  have hmean : mean logPK ≤ ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT + ∑ j, mean (logK j) := by
    calc mean logPK ≤ mean (fun s => logP s + ∑ j, logK j s) := mean_le_mean_of_le _ _ hPK
      _ = mean logP + ∑ j, mean (logK j) := by rw [mean_add_distrib, mean_sum_comm]
      _ ≤ _ := by gcongr; exact mean_le_of_le_const _ _ hP
  have hsum2 : ∑ j, mean (logK j) ≤ ∑ _j : Fin m, ∑ τ ∈ TT, topTerm (A τ) logOm
      + ∑ j : Fin m, ∑ τ ∈ T2, placeTerm (nu j τ) logOm
      + m * (C2 * Fintype.card ι * ((n:ℝ) + 1) * b' * L) := by
    calc ∑ j, mean (logK j) ≤ ∑ j : Fin m, (∑ τ ∈ TT, topTerm (A τ) logOm
      + ∑ τ ∈ T2, placeTerm (nu j τ) logOm + C2 * Fintype.card ι * ((n:ℝ) + 1) * b' * L) :=
          Finset.sum_le_sum fun j _ => key2 j
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have har := first_part_arithmetic_bound C₀ C2 C3 (Fintype.card ι) TT.card m t ((n:ℝ) + 1) b' L logT eta S hC
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast Finset.card_le_univ TT) hm1
    (by linarith) hb1 hL hT0 hN.logT_le hN.eta_nonneg hN.S_nonneg hmt hN.small hNL
  linarith

theorem zeta_proposition_first : PropZ_i := PropZ_i_of second_zeta_mean_bound third_zeta_application

private lemma zii_plus_nonneg {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) (i : Fin (κ + 1)) :
    0 ≤ plus lam i := by
  simp only [plus]
  exact sub_nonneg.2 (h (Fin.le_last i))

private lemma zii_plus0_le {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) :
    plus lam 0 ≤ wt (plus lam) := by
  unfold wt
  exact Finset.single_le_sum (f := plus lam) (fun i _ => zii_plus_nonneg lam h i) (Finset.mem_univ 0)

private lemma zii_log_le {a L v W : ℝ} (ha : 1 ≤ a) (hv : 1 ≤ v) (hL : 1 ≤ L)
    (hlog : Real.log (a * v) ≤ L) (hW0 : 0 < W) (hW : W ≤ 9 * a ^ 2) : Real.log W ≤ 10 * L := by
  have ha0 : 0 < a := by linarith
  have h1 : Real.log W ≤ Real.log (9 * a ^ 2) := Real.log_le_log hW0 hW
  have h2 : Real.log (9 * a ^ 2) = Real.log 9 + 2 * Real.log a := by
    rw [Real.log_mul (by norm_num) (pow_pos ha0 2).ne', Real.log_pow, Nat.cast_ofNat]
  have h3 : Real.log 9 ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 9)
    linarith
  have h4 : Real.log a ≤ L := by
    have : Real.log a ≤ Real.log (a * v) := Real.log_le_log ha0 (by nlinarith)
    linarith
  linarith

theorem zeta_proposition_second : PropZ_ii := by
  intro C₀ hC
  refine ⟨11 + C₀, ?_⟩
  intro ι X _ _ _ _ TT κ m t N lam A bt a b' L v logT logg eta S muM muV muDelta muNabla muMaxNabla
    hN hanti hTT hwt hwtp hwtp' hwt' hM hV hD hNab hMax
  have hL1 := hN.one_le_L
  have hv1 := hN.one_le_v
  have hb1 := hN.one_le_b'
  have hba := hN.b'_le_a
  have hT0 := hN.logT_nonneg
  have hS0 := hN.S_nonneg
  have hκ0 : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
  have hK1 : (1:ℝ) ≤ (κ:ℝ) + 1 := by linarith
  have hK0 : (0:ℝ) < (κ:ℝ) + 1 := by linarith
  have hKN : (κ:ℝ) + 1 ≤ N := by
    have : κ + 1 ≤ N := by rw [hN.N_eq]; exact Nat.le_add_right _ _
    exact_mod_cast this
  have hNL : (N:ℝ) * L ≤ b' := by linarith [hN.lin]
  have hNNL : (N:ℝ) ≤ N * L := by nlinarith
  have hKb : (κ:ℝ) + 1 ≤ b' := by linarith
  have hKa : (κ:ℝ) + 1 ≤ a := le_trans hKb hba
  have hSb : S ≤ b' := by
    have := hN.small
    have := hN.eta_nonneg
    have : (0:ℝ) ≤ (m:ℝ) * t := by positivity
    linarith
  have ha1 : 1 ≤ a := le_trans hb1 hba
  have haa : a ≤ a ^ 2 := by nlinarith
  have hlogK0 : 0 ≤ Real.log ((κ:ℝ) + 1) := Real.log_nonneg hK1
  have hKbS : 0 ≤ ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) :=
    mul_nonneg (mul_nonneg hK0.le (by linarith)) hlogK0
  have hZ4 : ∀ ρ, MeanSquareWeightBound (lam ρ) ≤ (if ρ ∈ TT then 2 * a * Real.log ((κ:ℝ) + 1) else 0)
      + (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) + 10 * ((κ:ℝ) + 1) ^ 2 * L) := by
    intro ρ
    have hp0 : (0:ℝ) ≤ (plus (lam ρ) 0 : ℝ) := by exact_mod_cast zii_plus_nonneg (lam ρ) (hanti ρ) 0
    have hpW : (plus (lam ρ) 0 : ℝ) ≤ (wt (plus (lam ρ)) : ℝ) := by
      exact_mod_cast zii_plus0_le (lam ρ) (hanti ρ)
    unfold MeanSquareWeightBound
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      obtain ⟨h1, h2, h3, h4⟩ := hTT ρ hρ
      have hw := hwtp ρ hρ
      have e1 : ((κ:ℝ) + 1) * (bt ρ + S) ≤ ((κ:ℝ) + 1) * (2 * (b' + S)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK0.le
      have hWb : (wt (plus (lam ρ)) : ℝ) ≤ 2 * a + 2 * (((κ:ℝ) + 1) * (b' + S)) := by linarith
      have e2 : ((κ:ℝ) + 1) * (b' + S) ≤ a * (2 * a) :=
        mul_le_mul hKa (by linarith) (by linarith) (by linarith)
      have hlog : Real.log ((plus (lam ρ) 0 : ℝ) + (κ:ℝ) + 1) ≤ 10 * L :=
        zii_log_le ha1 hv1 hL1 hN.log_av (by linarith) (by nlinarith)
      have f1 := mul_le_mul_of_nonneg_right hWb hlogK0
      have f2 := mul_le_mul_of_nonneg_left hlog (sq_nonneg ((κ:ℝ) + 1))
      nlinarith [f1, f2, hKbS]
    · rw [if_neg hρ]
      have hw := hwtp' ρ hρ
      have e1 : ((κ:ℝ) + 1 + 3) * S ≤ 4 * (((κ:ℝ) + 1) * (b' + S)) := by nlinarith
      have e2 : ((κ:ℝ) + 1 + 3) * S ≤ (4 * a) * a := mul_le_mul (by linarith) (by linarith) hS0 (by linarith)
      have hlog : Real.log ((plus (lam ρ) 0 : ℝ) + (κ:ℝ) + 1) ≤ 10 * L :=
        zii_log_le ha1 hv1 hL1 hN.log_av (by linarith) (by nlinarith)
      have f1 := mul_le_mul_of_nonneg_right (hw.trans e1) hlogK0
      have f2 := mul_le_mul_of_nonneg_left hlog (sq_nonneg ((κ:ℝ) + 1))
      nlinarith [f1, f2, hKbS]
  have hsumZ4 : ∑ ρ, MeanSquareWeightBound (lam ρ) ≤ (TT.card : ℝ) * (2 * a * Real.log ((κ:ℝ) + 1))
      + (Fintype.card ι : ℝ) * (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1)
        + 10 * ((κ:ℝ) + 1) ^ 2 * L) := by
    have e1 : ∑ ρ, (if ρ ∈ TT then 2 * a * Real.log ((κ:ℝ) + 1) else 0)
        = (TT.card : ℝ) * (2 * a * Real.log ((κ:ℝ) + 1)) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have e2 : ∑ _ρ : ι, (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) + 10 * ((κ:ℝ) + 1) ^ 2 * L)
        = (Fintype.card ι : ℝ) * (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1)
          + 10 * ((κ:ℝ) + 1) ^ 2 * L) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ∑ ρ, MeanSquareWeightBound (lam ρ) ≤ ∑ ρ, ((if ρ ∈ TT then 2 * a * Real.log ((κ:ℝ) + 1) else 0)
          + (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) + 10 * ((κ:ℝ) + 1) ^ 2 * L)) :=
          Finset.sum_le_sum fun ρ _ => hZ4 ρ
      _ = _ := by rw [Finset.sum_add_distrib, e1, e2]
  have hwtbound : ∀ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT
      ≤ (if ρ ∈ TT then A ρ / ((κ:ℝ) + 1) * logT else 0) + (1 + C₀) * S * logT := by
    intro ρ
    have h3 : 0 ≤ C₀ * S * logT := mul_nonneg (mul_nonneg hC hS0) hT0
    have h4 : 0 ≤ S * logT := mul_nonneg hS0 hT0
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      have h := hwt ρ hρ
      have h1 : (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) ≤ A ρ / ((κ:ℝ) + 1) + S := by
        rw [div_le_iff₀ hK0, add_mul, div_mul_cancel₀ _ hK0.ne']
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hT0
      linarith
    · rw [if_neg hρ]
      have h := hwt' ρ hρ
      have h1 : (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) ≤ C₀ * S := by
        rw [div_le_iff₀ hK0]
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hT0
      linarith
  have hsumwt : ∑ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT
      ≤ ∑ τ ∈ TT, A τ / ((κ:ℝ) + 1) * logT + (Fintype.card ι : ℝ) * ((1 + C₀) * S * logT) := by
    have e1 : ∑ ρ, (if ρ ∈ TT then A ρ / ((κ:ℝ) + 1) * logT else 0)
        = ∑ τ ∈ TT, A τ / ((κ:ℝ) + 1) * logT := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have e2 : ∑ _ρ : ι, (1 + C₀) * S * logT = (Fintype.card ι : ℝ) * ((1 + C₀) * S * logT) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ∑ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT
        ≤ ∑ ρ, ((if ρ ∈ TT then A ρ / ((κ:ℝ) + 1) * logT else 0) + (1 + C₀) * S * logT) :=
          Finset.sum_le_sum fun ρ _ => hwtbound ρ
      _ = _ := by rw [Finset.sum_add_distrib, e1, e2]
  have hmean : muM = -(∑ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT) + ∑ ρ, muDelta ρ := by
    rw [hM]
    have hc : (0:ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
    unfold mean
    simp only [hV]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hc.ne']
  have hDel : -(∑ ρ, MeanSquareWeightBound (lam ρ)) ≤ ∑ ρ, muDelta ρ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun ρ _ => by rw [hD ρ]; linarith [hNab ρ, hMax ρ]
  have hcard0 : (0:ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have n1 : 0 ≤ (TT.card : ℝ) * a * Real.log ((κ:ℝ) + 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hlogK0
  have m1 : 0 ≤ C₀ * ((TT.card : ℝ) * a * Real.log ((κ:ℝ) + 1)) := mul_nonneg hC n1
  have n2 : 0 ≤ (Fintype.card ι : ℝ) * S * logT := mul_nonneg (mul_nonneg hcard0 hS0) hT0
  have n3 : 0 ≤ (Fintype.card ι : ℝ) * (((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1)) :=
    mul_nonneg hcard0 hKbS
  have m3 : 0 ≤ C₀ * ((Fintype.card ι : ℝ) * (((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1))) :=
    mul_nonneg hC n3
  have n4 : 0 ≤ (Fintype.card ι : ℝ) * (((κ:ℝ) + 1) ^ 2 * L) :=
    mul_nonneg hcard0 (mul_nonneg (sq_nonneg _) (by linarith))
  have m4 : 0 ≤ C₀ * ((Fintype.card ι : ℝ) * (((κ:ℝ) + 1) ^ 2 * L)) := mul_nonneg hC n4
  linarith [hmean, hDel, hsumZ4, hsumwt, n1, m1, n2, n3, m3, n4, m4]

private lemma positive_part_head_le_weight {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) :
    0 ≤ plus lam 0 ∧ plus lam 0 ≤ wt (plus lam) := ⟨zii_plus_nonneg lam h 0, zii_plus0_le lam h⟩

private lemma ziii_log {a L v x : ℝ} (ha : 1 ≤ a) (hv : 1 ≤ v) (hL : 1 ≤ L)
    (hlog : Real.log (a * v) ≤ L) (hx0 : 0 < x) (hx : x ≤ 7 * a ^ 2) : Real.log x ≤ 8 * L := by
  have ha0 : 0 < a := by linarith
  have h1 : Real.log x ≤ Real.log (7 * a ^ 2) := Real.log_le_log hx0 hx
  have h2 : Real.log (7 * a ^ 2) = Real.log 7 + 2 * Real.log a := by
    rw [Real.log_mul (by norm_num) (pow_pos ha0 2).ne', Real.log_pow, Nat.cast_ofNat]
  have h3 : Real.log 7 ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 7)
    linarith
  have h4 : Real.log a ≤ L := by
    have : Real.log a ≤ Real.log (a * v) := Real.log_le_log ha0 (by nlinarith)
    linarith
  linarith

private lemma ziii_place {C₀ K b' S L lkv logT W lst lg U : ℝ} (hC : 0 ≤ C₀) (hK : 1 ≤ K)
    (hlkv : 0 ≤ lkv) (hT : 0 ≤ logT)
    (hW : W ≤ U + 4 * K * (b' + S)) (hlg : lg ≤ 8 * L) (hlst : lst ≤ (2 + C₀) * (b' + S)) :
    W * (C₀ * lkv) + K ^ 2 * lg + lst * logT ≤
      U * (C₀ * lkv) + (4 * C₀ * K * (b' + S) * lkv + (2 + C₀) * (b' + S) * logT + 8 * K ^ 2 * L) := by
  have h0 : 0 ≤ C₀ * lkv := mul_nonneg hC hlkv
  have h1 := mul_le_mul_of_nonneg_right hW h0
  have h2 := mul_le_mul_of_nonneg_left hlg (sq_nonneg K)
  have h3 := mul_le_mul_of_nonneg_right hlst hT
  linarith [h1, h2, h3]

private lemma ziii_top {C₀ K a b' S L v logT W p lst At bt : ℝ} (hC : 0 ≤ C₀) (hK : 1 ≤ K)
    (hKa : K ≤ a) (hb1 : 1 ≤ b') (hba : b' ≤ a) (hS : 0 ≤ S) (hSb : S ≤ b') (hL : 1 ≤ L) (hv : 1 ≤ v)
    (hlog : Real.log (a * v) ≤ L) (hT : 0 ≤ logT) (hp0 : 0 ≤ p) (hpW : p ≤ W)
    (hA2 : At ≤ 2 * a) (hbt2 : bt ≤ 2 * b') (hW : W ≤ At + K * (bt + S)) (hl : lst ≤ bt) :
    W * (C₀ * Real.log (K * v)) + K ^ 2 * Real.log (p + K) + lst * logT ≤
      2 * a * (C₀ * Real.log (K * v)) + (4 * C₀ * K * (b' + S) * Real.log (K * v)
        + (2 + C₀) * (b' + S) * logT + 8 * K ^ 2 * L) := by
  have hK0 : 0 ≤ K := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hlkv : 0 ≤ Real.log (K * v) := Real.log_nonneg (by nlinarith)
  have hbS : bt + S ≤ 3 * a := by linarith
  have hKbt : K * (bt + S) ≤ a * (3 * a) :=
    (mul_le_mul_of_nonneg_left hbS hK0).trans (mul_le_mul_of_nonneg_right hKa (by linarith))
  have hW' : W ≤ 2 * a + 4 * K * (b' + S) := by
    have : K * (bt + S) ≤ K * (4 * (b' + S)) := mul_le_mul_of_nonneg_left (by linarith) hK0
    linarith
  have haa : a ≤ a ^ 2 := by nlinarith
  have hlg : Real.log (p + K) ≤ 8 * L :=
    ziii_log (by linarith) hv hL hlog (by linarith) (by nlinarith)
  have hlst : lst ≤ (2 + C₀) * (b' + S) := by
    nlinarith [mul_nonneg hC (by linarith : (0:ℝ) ≤ b' + S)]
  have := ziii_place (U := 2 * a) hC hK hlkv hT hW' hlg hlst
  linarith

private lemma ziii_other {C₀ K a b' S L v logT W p lst : ℝ} (hC : 0 ≤ C₀) (hK : 1 ≤ K)
    (hKa : K ≤ a) (hb1 : 1 ≤ b') (hba : b' ≤ a) (hS : 0 ≤ S) (hSb : S ≤ b') (hL : 1 ≤ L) (hv : 1 ≤ v)
    (hlog : Real.log (a * v) ≤ L) (hT : 0 ≤ logT) (hp0 : 0 ≤ p) (hpW : p ≤ W)
    (hW : W ≤ (K + 3) * S) (hl : lst ≤ C₀ * S) :
    W * (C₀ * Real.log (K * v)) + K ^ 2 * Real.log (p + K) + lst * logT ≤
      0 + (4 * C₀ * K * (b' + S) * Real.log (K * v)
        + (2 + C₀) * (b' + S) * logT + 8 * K ^ 2 * L) := by
  have hK0 : 0 ≤ K := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hlkv : 0 ≤ Real.log (K * v) := Real.log_nonneg (by nlinarith)
  have hW' : W ≤ 0 + 4 * K * (b' + S) := by
    have h1 : 1 * S ≤ K * S := mul_le_mul_of_nonneg_right hK hS
    have h2 : 0 ≤ K * b' := mul_nonneg hK0 (by linarith)
    nlinarith
  have hK3 : K + 3 ≤ 4 * a := by linarith
  have hSa : S ≤ a := by linarith
  have hKS : (K + 3) * S ≤ 4 * a * a := mul_le_mul hK3 hSa hS (by linarith)
  have haa : a ≤ a ^ 2 := by nlinarith
  have hlg : Real.log (p + K) ≤ 8 * L :=
    ziii_log (by linarith) hv hL hlog (by linarith) (by nlinarith)
  have hlst : lst ≤ (2 + C₀) * (b' + S) := by
    nlinarith [mul_nonneg hC (by linarith : (0:ℝ) ≤ b')]
  have := ziii_place (U := 0) hC hK hlkv hT hW' hlg hlst
  linarith

private lemma final_part_arithmetic_bound {C₀ nT f a lkv K b' S logT L : ℝ} (hC : 0 ≤ C₀) (hnT : 0 ≤ nT) (hf : 0 ≤ f)
    (ha : 0 ≤ a) (hlkv : 0 ≤ lkv) (hK : 0 ≤ K) (hbS : 0 ≤ b' + S) (hT : 0 ≤ logT) (hL : 0 ≤ L) :
    nT * (2 * a * (C₀ * lkv)) + f * (4 * C₀ * K * (b' + S) * lkv + (2 + C₀) * (b' + S) * logT
        + 8 * K ^ 2 * L) ≤
      (8 + 4 * C₀) * nT * a * lkv + (8 + 4 * C₀) * f * (b' + S) * (K * lkv + logT)
        + (8 + 4 * C₀) * f * K ^ 2 * L := by
  have p1 : 0 ≤ nT * a * lkv := mul_nonneg (mul_nonneg hnT ha) hlkv
  have q1 : 0 ≤ C₀ * (nT * a * lkv) := mul_nonneg hC p1
  have p2 : 0 ≤ f * (b' + S) * K * lkv := mul_nonneg (mul_nonneg (mul_nonneg hf hbS) hK) hlkv
  have p3 : 0 ≤ f * (b' + S) * logT := mul_nonneg (mul_nonneg hf hbS) hT
  have q3 : 0 ≤ C₀ * (f * (b' + S) * logT) := mul_nonneg hC p3
  have q4 : 0 ≤ C₀ * (f * K ^ 2 * L) := mul_nonneg hC (mul_nonneg (mul_nonneg hf (sq_nonneg K)) hL)
  linarith [p1, q1, p2, p3, q3, q4]

theorem zeta_proposition_third : PropZ_iii := by
  intro C₀ hC
  refine ⟨8 + 4 * C₀, ?_⟩
  intro ι X _ _ _ _ TT κ m t N lam A bt a b' L v logT logg eta S muMaxM muMaxV hN hanti hTT hWT hlT
    hWo hlo hex hV
  obtain ⟨c, hc⟩ := hex
  have hL := hN.one_le_L
  have hv := hN.one_le_v
  have hb1 := hN.one_le_b'
  have hba := hN.b'_le_a
  have hT := hN.logT_nonneg
  have hS := hN.S_nonneg
  have ha : 1 ≤ a := le_trans hb1 hba
  have hmt : (0:ℝ) ≤ (m : ℝ) * t := by positivity
  have hSb : S ≤ b' := by have := hN.small; have := hN.eta_nonneg; linarith
  have hKN : (κ : ℝ) + 1 ≤ N := by
    have : κ + 1 ≤ N := by rw [hN.N_eq]; exact Nat.le_add_right _ _
    exact_mod_cast this
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hNb : (N : ℝ) ≤ b' := by
    have h1 := hN.lin
    have h2 : (N : ℝ) * 1 ≤ N * L := mul_le_mul_of_nonneg_left hL hN0
    linarith
  have hK1 : (1:ℝ) ≤ (κ : ℝ) + 1 := by
    have : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
    linarith
  have hKa : (κ : ℝ) + 1 ≤ a := by linarith
  have hlkv : 0 ≤ Real.log (((κ : ℝ) + 1) * v) := Real.log_nonneg (by nlinarith)
  have key : ∀ ρ, ((wt (plus (lam ρ)) : ℝ) * (C₀ * Real.log (((κ : ℝ) + 1) * v))
        + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus (lam ρ) 0 : ℝ) + (κ : ℝ) + 1)
        + |(lam ρ (Fin.last κ) : ℝ)| * logT) ≤
      (if ρ ∈ TT then 2 * a * (C₀ * Real.log (((κ : ℝ) + 1) * v)) else 0)
        + (4 * C₀ * ((κ : ℝ) + 1) * (b' + S) * Real.log (((κ : ℝ) + 1) * v)
          + (2 + C₀) * (b' + S) * logT + 8 * ((κ : ℝ) + 1) ^ 2 * L) := by
    intro ρ
    obtain ⟨hp0, hpW⟩ := positive_part_head_le_weight (lam ρ) (hanti ρ)
    have hp0' : (0:ℝ) ≤ (plus (lam ρ) 0 : ℝ) := by exact_mod_cast hp0
    have hpW' : (plus (lam ρ) 0 : ℝ) ≤ (wt (plus (lam ρ)) : ℝ) := by exact_mod_cast hpW
    rw [add_assoc ((plus (lam ρ) 0 : ℤ) : ℝ) (κ : ℝ) 1]
    by_cases hρ : ρ ∈ TT
    · obtain ⟨hA1, hA2, hbt1, hbt2⟩ := hTT ρ hρ
      rw [if_pos hρ]
      exact ziii_top hC hK1 hKa hb1 hba hS hSb hL hv hN.log_av hT hp0' hpW' hA2 hbt2 (hWT ρ hρ)
        (hlT ρ hρ)
    · rw [if_neg hρ]
      exact ziii_other hC hK1 hKa hb1 hba hS hSb hL hv hN.log_av hT hp0' hpW' (hWo ρ hρ) (hlo ρ hρ)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun ρ _ => key ρ)
  have hrhs : ∀ x y : ℝ, ∑ ρ : ι, ((if ρ ∈ TT then x else 0) + y)
      = (TT.card : ℝ) * x + (Fintype.card ι : ℝ) * y := by
    intro x y
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ]
  rw [hrhs] at hsum
  refine le_trans (le_trans hc (le_trans (hV c) hsum)) ?_
  exact final_part_arithmetic_bound hC (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith) hlkv (by linarith)
    (by linarith) hT (by linarith)

set_option maxHeartbeats 800000 in

theorem zeta_proposition_tail : Formalism.HermitianLattices.TraceIntegrality.PropZ_tail := by
  intro C₀ hC
  refine ⟨10 + 5 * C₀, ?_⟩
  intro f nT k m t N x b a b' L v logT logg eta S sA hN hb hax hnT1 hnTf hsA0 hsA
  have hL1 := hN.one_le_L
  have hv1 := hN.one_le_v
  have hb1 := hN.one_le_b'
  have hba := hN.b'_le_a
  have hT0 := hN.logT_nonneg
  have hTle := hN.logT_le
  have hS0 := hN.S_nonneg
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hN.one_le_k
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hN.one_le_m
  have hkN : (k:ℝ) ≤ N := by
    have : k ≤ N := by rw [hN.N_eq]; exact Nat.le_add_right _ _
    exact_mod_cast this
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hN1 : (1:ℝ) ≤ N := le_trans hk1 hkN
  have hNL : (N:ℝ) * L ≤ b' := by linarith only [hN.lin, hT0]
  have hNNL : (N:ℝ) ≤ N * L := le_mul_of_one_le_right hN0 hL1
  have hkb : (k:ℝ) ≤ b' := by linarith only [hkN, hNNL, hNL]
  have hka : (k:ℝ) ≤ a := le_trans hkb hba
  have hSb : S ≤ b' := by
    have h1 := hN.small
    have h2 := hN.eta_nonneg
    have h3 : (0:ℝ) ≤ (m:ℝ) * t := by positivity
    linarith only [h1, h2, h3]
  have hnT : (1:ℝ) ≤ nT := by exact_mod_cast hnT1
  have hnT0' : (0:ℝ) ≤ nT := by linarith only [hnT]
  have hm0' : (0:ℝ) ≤ m := by linarith only [hm1]
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  have hL0 : (0:ℝ) ≤ L := by linarith only [hL1]
  have hb0 : (0:ℝ) ≤ b' := by linarith only [hb1]
  have hk0 : (0:ℝ) ≤ k := by linarith only [hk1]
  have ha0 : (0:ℝ) ≤ a := by linarith only [hb1, hba]
  have hv0 : (0:ℝ) ≤ v := by linarith only [hv1]
  have hbS0 : (0:ℝ) ≤ b' + S := by linarith only [hb0, hS0]
  have hlogk : Real.log k ≤ L := by
    have : Real.log k ≤ Real.log (a * v) :=
      Real.log_le_log (by linarith only [hk1]) (hka.trans (le_mul_of_one_le_right ha0 hv1))
    linarith only [this, hN.log_av]
  have hlogkv0 : 0 ≤ Real.log (k * v) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hk1 hv1)
  have hlogkv : Real.log (k * v) ≤ L := by
    have : Real.log (k * v) ≤ Real.log (a * v) :=
      Real.log_le_log (mul_pos (by linarith only [hk1]) (by linarith only [hv1]))
        (mul_le_mul_of_nonneg_right hka hv0)
    linarith only [this, hN.log_av]
  have hG0 : 0 ≤ (f:ℝ) * N * b' * L := mul_nonneg (mul_nonneg (mul_nonneg hf0 hN0) hb0) hL0
  have hG : (f:ℝ) * N * b' * L ≤ f * m * N * b' * L := by
    have := mul_le_mul_of_nonneg_left hm1 hG0
    linarith only [this]
  have t1 : sA / k * logT ≤ 2 * C₀ * (a * nT * m * L / k) := by
    have s1 : sA / k ≤ 2 * a * nT / k := by gcongr
    have s0 : 0 ≤ 2 * a * nT / k :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0) hnT0') hk0
    calc sA / k * logT ≤ 2 * a * nT / k * logT := mul_le_mul_of_nonneg_right s1 hT0
      _ ≤ 2 * a * nT / k * (C₀ * m * L) := mul_le_mul_of_nonneg_left hTle s0
      _ = 2 * C₀ * (a * nT * m * L / k) := by ring
  have t2 : (nT:ℝ) * a * Real.log k ≤ nT * a * L :=
    mul_le_mul_of_nonneg_left hlogk (mul_nonneg hnT0' ha0)
  have t6 : (nT:ℝ) * a * Real.log (k * v) ≤ nT * a * L :=
    mul_le_mul_of_nonneg_left hlogkv (mul_nonneg hnT0' ha0)
  have t3 : (f:ℝ) * k * (b' + S) * Real.log k ≤ 2 * ((f:ℝ) * N * b' * L) := by
    have u1 : (k:ℝ) * (b' + S) ≤ N * (2 * b') :=
      mul_le_mul hkN (by linarith only [hSb]) hbS0 hN0
    have u2 : (f:ℝ) * k * (b' + S) * Real.log k ≤ f * k * (b' + S) * L :=
      mul_le_mul_of_nonneg_left hlogk (mul_nonneg (mul_nonneg hf0 hk0) hbS0)
    have u3 : (f:ℝ) * (k * (b' + S)) * L ≤ f * (N * (2 * b')) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u1 hf0) hL0
    linarith only [u2, u3]
  have t4 : (f:ℝ) * S * logT ≤ C₀ * ((f:ℝ) * m * N * b' * L) := by
    have u1 : S * logT ≤ b' * (C₀ * m * L) := mul_le_mul hSb hTle hT0 hb0
    have u2 : (f:ℝ) * (S * logT) ≤ f * (b' * (C₀ * m * L)) := mul_le_mul_of_nonneg_left u1 hf0
    have u3 : 0 ≤ (f:ℝ) * b' * C₀ * m * L :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf0 hb0) hC) hm0') hL0
    have u4 := mul_nonneg u3 (sub_nonneg.2 hN1)
    linarith only [u2, u4]
  have t5 : (f:ℝ) * (k:ℝ) ^ 2 * L ≤ (f:ℝ) * N * b' * L := by
    have u1 : (k:ℝ) * k ≤ N * b' := mul_le_mul hkN hkb hk0 hN0
    have u2 : (f:ℝ) * (k * k) * L ≤ f * (N * b') * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u1 hf0) hL0
    linarith only [u2]
  have t7 : (f:ℝ) * (b' + S) * (k * Real.log (k * v) + logT)
      ≤ 2 * ((f:ℝ) * N * b' * L) + 2 * C₀ * ((f:ℝ) * m * N * b' * L) := by
    have u1 : (k:ℝ) * Real.log (k * v) ≤ N * L :=
      (mul_le_mul_of_nonneg_left hlogkv hk0).trans (mul_le_mul_of_nonneg_right hkN hL0)
    have u2 : logT ≤ C₀ * m * N * L := by
      have h0 : 0 ≤ C₀ * m * L := mul_nonneg (mul_nonneg hC hm0') hL0
      calc logT ≤ C₀ * m * L := hTle
        _ = C₀ * m * L * 1 := by ring
        _ ≤ C₀ * m * L * N := mul_le_mul_of_nonneg_left hN1 h0
        _ = C₀ * m * N * L := by ring
    have u3 : 0 ≤ (k:ℝ) * Real.log (k * v) + logT := by
      have h0 := mul_nonneg hk0 hlogkv0
      linarith only [h0, hT0]
    have u4 : (b' + S) * ((k:ℝ) * Real.log (k * v) + logT) ≤ (2 * b') * (N * L + C₀ * m * N * L) :=
      mul_le_mul (by linarith only [hSb]) (by linarith only [u1, u2]) u3 (by linarith only [hb0])
    have u5 := mul_le_mul_of_nonneg_left u4 hf0
    linarith only [u5]
  have hD : (0:ℝ) < nT * m * b :=
    mul_pos (mul_pos (by linarith only [hnT]) (by linarith only [hm1])) hb
  rw [div_le_iff₀ hD]
  have hm0 : (m:ℝ) ≠ 0 := (by linarith only [hm1] : (0:ℝ) < m).ne'
  have hk0' : (k:ℝ) ≠ 0 := (by linarith only [hk1] : (0:ℝ) < k).ne'
  have hnT0 : (nT:ℝ) ≠ 0 := (by linarith only [hnT] : (0:ℝ) < nT).ne'
  have hb0' : b ≠ 0 := hb.ne'
  have hE : (10 + 5 * C₀) * (x * L / m + x * L / k + f * N * b' * L / (nT * b)) * (nT * m * b)
      = (10 + 5 * C₀) * (a * nT * L + a * nT * m * L / k + f * m * N * b' * L) := by
    rw [hax]
    field_simp
  rw [hE]
  have hQ1 : 0 ≤ a * nT * L := mul_nonneg (mul_nonneg ha0 hnT0') hL0
  have hQ2 : 0 ≤ a * nT * m * L / k :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha0 hnT0') hm0') hL0) hk0
  have hQ3 : 0 ≤ (f:ℝ) * m * N * b' * L := by linarith only [hG0, hG]
  have r1 := mul_nonneg hC hQ1
  have r2 := mul_nonneg hC hQ2
  have r3 := mul_nonneg hC hQ3
  linarith only [t1, t2, t3, t4, t5, t6, t7, hG, hQ1, hQ2, hQ3, r1, r2, r3]

end Formalism.HermitianLattices.TraceIntegrality
