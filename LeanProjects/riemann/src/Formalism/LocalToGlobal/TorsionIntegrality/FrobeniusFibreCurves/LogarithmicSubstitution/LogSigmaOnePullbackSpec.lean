import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst

noncomputable section

namespace Formalism.L2.Th1.B.Ph

open PowerSeries

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem hs {l : PowerSeries K} (hl : constantCoeff l = 0) : HasSubst l := by
  exact HasSubst.of_constantCoeff_zero' hl

theorem psubst_neg {l : PowerSeries K} (hl : constantCoeff l = 0) (f : PowerSeries K) :
    subst l (-f) = -subst l f := by
  rw [← coe_substAlgHom (hs hl), map_neg]

theorem psubst_C_mul {l : PowerSeries K} (hl : constantCoeff l = 0) (c : K) (f : PowerSeries K) :
    subst l (C c * f) = C c * subst l f := by
  rw [subst_mul (hs hl), subst_C]
  rfl

theorem constantCoeff_psubst {l : PowerSeries K} (hl : constantCoeff l = 0) (g : PowerSeries K) :
    constantCoeff (subst l g) = constantCoeff g := by
  have h0 : constantCoeff (subst l (g - C (constantCoeff g))) = 0 :=
    constantCoeff_subst_eq_zero hl _ (by simp)
  have hg : g = C (constantCoeff g) + (g - C (constantCoeff g)) := by ring
  conv_lhs => rw [hg]
  rw [subst_add (hs hl), map_add, h0, subst_C, add_zero]
  rfl

theorem psubst_fExp {l f : PowerSeries K} (hl : constantCoeff l = 0) (hf : constantCoeff f = 0) :
    subst l (fExp f) = fExp (subst l f) := by
  unfold fExp
  exact subst_comp_subst_apply (hs hf) (hs hl) _

theorem psubst_fLog {l g : PowerSeries K} (hl : constantCoeff l = 0) (hg : constantCoeff g = 1) :
    subst l (fLog g) = fLog (subst l g) := by
  have h1 : constantCoeff (g - 1) = 0 := by rw [map_sub, hg, map_one, sub_self]
  unfold fLog
  rw [subst_comp_subst_apply (hs h1) (hs hl), subst_sub (hs hl), psubst_one (hs hl)]

theorem psubst_neg_of_even {f l : PowerSeries K} (h : ∀ n, Odd n → coeff n f = 0)
    (hl : constantCoeff l = 0) : subst (-l) f = subst l f := by
  have hX : HasSubst ((-1 : K) • (X : PowerSeries K)) := HasSubst.smul_X' _
  have e1 : subst l ((-1 : K) • (X : PowerSeries K)) = -l := by
    rw [subst_smul (hs hl), subst_X (hs hl), neg_one_smul]
  have e2 : rescale (-1 : K) f = f := by
    ext n
    rw [coeff_rescale]
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow, one_mul]
    · rw [h n ho, mul_zero]
  rw [← e1, ← subst_comp_subst_apply hX (hs hl), ← rescale_eq_subst, e2]

theorem coeff_prim_succ (f : PowerSeries K) (n : ℕ) :
    coeff (n + 1) (prim f) = coeff n f / ((n + 1 : ℕ) : K) := by
  simp [prim]

theorem coeff_zero_prim (f : PowerSeries K) : coeff 0 (prim f) = 0 := by
  simp [prim]

theorem prim_prim_even {f : PowerSeries K} (h : ∀ n, Odd n → coeff n f = 0) :
    ∀ n, Odd n → coeff n (prim (prim f)) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := hn
  rw [coeff_prim_succ]
  rcases k with _ | k
  · simp [coeff_zero_prim]
  · have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [e, coeff_prim_succ, h (2 * k + 1) (odd_two_mul_add_one k)]
    simp

theorem constantCoeff_sigS (P : PowerSeries K) : constantCoeff (sigS P) = 0 := by
  rw [sigS, map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_prim, neg_zero]

theorem constantCoeff_sig1S (e1 kap : K) (w : PowerSeries K) :
    constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  rw [sigmaOneSeries, map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_prim, neg_zero]

theorem sigS_even {P : PowerSeries K} (hP : ∀ n, Odd n → coeff n P = 0) :
    ∀ n, Odd n → coeff n (sigS P) = 0 := by
  intro n hn
  rw [sigS, map_neg, prim_prim_even hP n hn, neg_zero]

theorem sigmaOneLogPart_even (e1 kap : K) {w : PowerSeries K} (hw : ∀ n, Odd n → coeff n w = 0) :
    ∀ n, Odd n → coeff n (sigmaOneSeries e1 kap w) = 0 := by
  intro n hn
  have hev : ∀ m, Odd m → coeff m (C e1 + C kap * w) = 0 := by
    intro m hm
    simp [coeff_C, coeff_C_mul, hw m hm, hm.pos.ne']
  rw [sigmaOneSeries, map_neg, prim_prim_even hev n hn, neg_zero]

theorem X_mul_lU {l : PowerSeries K} (hl : constantCoeff l = 0) : X * lU l = l := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, hl]
  · rw [coeff_succ_X_mul, lU, coeff_mk]

theorem constantCoeff_lU (l : PowerSeries K) : constantCoeff (lU l) = coeff 1 l := by
  rw [← coeff_zero_eq_constantCoeff_apply, lU, coeff_mk]

theorem constantCoeff_gauss (c : K) {l : PowerSeries K} (hl : constantCoeff l = 0) :
    constantCoeff (-(C c * l ^ 2)) = 0 := by
  simp [hl]

theorem psubst_gauss (c : K) {l : PowerSeries K} (hl : constantCoeff l = 0) :
    subst l (fExp (-(C c * X ^ 2))) = fExp (-(C c * l ^ 2)) := by
  rw [psubst_fExp hl (by simp), psubst_neg hl, psubst_C_mul hl, subst_pow (hs hl), subst_X (hs hl)]

theorem constantCoeff_phO (s2 : K) (P : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) (hl1 : coeff 1 l = 1) : constantCoeff (phO s2 P l) = 0 := by
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rw [hl1] at this
    exact this
  have hF : constantCoeff (fLog (lU l)) = 0 := constantCoeff_fLog hlu
  rw [phO, map_sub, map_add, map_neg, constantCoeff_psubst hl, constantCoeff_sigS, map_mul, map_pow, hl, hF]
  simp

theorem constantCoeff_phE (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) : constantCoeff (phE s2 e1 kap w l) = 0 := by
  rw [phE, map_add, map_neg, constantCoeff_psubst hl, constantCoeff_sig1S, map_mul, map_pow, hl]
  simp

end Alg

theorem logSigmaPullbackSpec : PhODef := by
  intro K _ _ s2 P l hl hl1
  refine ⟨constantCoeff_phO s2 P hl hl1, ?_⟩
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rw [hl1] at this
    exact this
  have hA : constantCoeff (fLog (lU l)) = 0 := constantCoeff_fLog hlu
  have hB : constantCoeff (subst l (sigS P)) = 0 := by rw [constantCoeff_psubst hl, constantCoeff_sigS]
  have hC : constantCoeff (-(C (s2 / 2) * l ^ 2)) = 0 := constantCoeff_gauss _ hl
  have hAB : constantCoeff (fLog (lU l) + subst l (sigS P)) = 0 := by rw [map_add, hA, hB, add_zero]
  have e : -phO s2 P l = fLog (lU l) + subst l (sigS P) + -(C (s2 / 2) * l ^ 2) := by
    rw [phO]
    ring
  rw [sgStar, sigma, subst_mul (hs hl), subst_mul (hs hl), subst_X (hs hl),
    psubst_fExp hl (constantCoeff_sigS P), psubst_gauss _ hl]
  calc l * fExp (subst l (sigS P)) * fExp (-(C (s2 / 2) * l ^ 2))
      = X * fExp (fLog (lU l)) * fExp (subst l (sigS P)) * fExp (-(C (s2 / 2) * l ^ 2)) := by
        rw [fExp_fLog hlu, X_mul_lU hl]
    _ = X * fExp (-phO s2 P l) := by
        rw [e, fExp_add hAB hC, fExp_add hA hB]
        ring

theorem logSigmaOnePullbackSpec : PhEDef := by
  intro K _ _ s2 e1 kap w l hl
  refine ⟨constantCoeff_phE s2 e1 kap w hl, ?_⟩
  have hB : constantCoeff (-subst l (sigmaOneSeries e1 kap w)) = 0 := by
    rw [map_neg, constantCoeff_psubst hl, constantCoeff_sig1S, neg_zero]
  have hC : constantCoeff (C (s2 / 2) * l ^ 2) = 0 := by simp [hl]
  have hB' : constantCoeff (subst l (sigmaOneSeries e1 kap w)) = 0 := by
    rw [constantCoeff_psubst hl, constantCoeff_sig1S]
  have hC' : constantCoeff (-(C (s2 / 2) * l ^ 2)) = 0 := constantCoeff_gauss _ hl
  rw [subst_mul (hs hl), sigma1, psubst_fExp hl (constantCoeff_sig1S _ _ _), psubst_gauss _ hl,
    ← fExp_add hB' hC']
  congr 1
  rw [phE]
  ring

section Parity

variable {K : Type} [Field K] [CharZero K]

theorem phO_inv_sub (s2 : K) {P l i : PowerSeries K} (hP : ∀ n, Odd n → coeff n P = 0)
    (hl : constantCoeff l = 0) (hl1 : coeff 1 l = 1) (hi : constantCoeff i = 0)
    (hli : subst i l = -l) :
    subst i (phO s2 P l) - phO s2 P l = fLog (lU l) - fLog (subst i (lU l)) := by
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rw [hl1] at this
    exact this
  rw [phO, subst_sub (hs hi), subst_add (hs hi), psubst_neg hi, psubst_C_mul hi, subst_pow (hs hi),
    hli, subst_comp_subst_apply (hs hl) (hs hi), hli, psubst_neg_of_even (sigS_even hP) hl,
    psubst_fLog hi hlu, neg_sq]
  ring

theorem fExp_phO_inv_sub (s2 : K) {P l i : PowerSeries K} (hP : ∀ n, Odd n → coeff n P = 0)
    (hl : constantCoeff l = 0) (hl1 : coeff 1 l = 1) (hi : constantCoeff i = 0)
    (hli : subst i l = -l) :
    fExp (subst i (phO s2 P l) - phO s2 P l) = -lU i := by
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rw [hl1] at this
    exact this
  have hblu : MvPowerSeries.constantCoeff (subst i (lU l)) = 1 := by
    have := constantCoeff_psubst hi (lU l)
    exact this.trans hlu
  have hA : MvPowerSeries.constantCoeff (fLog (lU l)) = 0 := constantCoeff_fLog hlu
  have hB : MvPowerSeries.constantCoeff (fLog (subst i (lU l))) = 0 := constantCoeff_fLog hblu
  have hAB : MvPowerSeries.constantCoeff (fLog (lU l) - fLog (subst i (lU l))) = 0 := by
    rw [map_sub, hA, hB, sub_zero]
  rw [phO_inv_sub s2 hP hl hl1 hi hli]
  have hb0 : subst i (lU l) ≠ 0 := by
    intro h
    rw [h, map_zero] at hblu
    exact zero_ne_one hblu
  have key1 : fExp (fLog (lU l) - fLog (subst i (lU l))) * subst i (lU l) = lU l := by
    calc fExp (fLog (lU l) - fLog (subst i (lU l))) * subst i (lU l)
        = fExp (fLog (lU l) - fLog (subst i (lU l))) * fExp (fLog (subst i (lU l))) := by
          rw [fExp_fLog hblu]
      _ = fExp (fLog (lU l) - fLog (subst i (lU l)) + fLog (subst i (lU l))) := (fExp_add hAB hB).symm
      _ = lU l := by rw [sub_add_cancel, fExp_fLog hlu]
  have h1 : subst i (X * lU l) = subst i l := by rw [X_mul_lU hl]
  rw [subst_mul (hs hi), subst_X (hs hi), hli] at h1
  have key2 : -lU i * subst i (lU l) = lU l := by
    have h2 : X * (-lU i * subst i (lU l)) = X * lU l := by
      calc X * (-lU i * subst i (lU l)) = -((X * lU i) * subst i (lU l)) := by ring
        _ = -(i * subst i (lU l)) := by rw [X_mul_lU hi]
        _ = X * lU l := by rw [h1, neg_neg, X_mul_lU hl]
    exact mul_left_cancel₀ X_ne_zero h2
  apply mul_right_cancel₀ hb0
  rw [key1, key2]

theorem phE_inv (s2 e1 kap : K) {w l i : PowerSeries K} (hw : ∀ n, Odd n → coeff n w = 0)
    (hl : constantCoeff l = 0) (hi : constantCoeff i = 0) (hli : subst i l = -l) :
    subst i (phE s2 e1 kap w l) = phE s2 e1 kap w l := by
  rw [phE, subst_add (hs hi), psubst_neg hi, psubst_C_mul hi, subst_pow (hs hi), hli,
    subst_comp_subst_apply (hs hl) (hs hi), hli, psubst_neg_of_even (sigmaOneLogPart_even e1 kap hw) hl, neg_sq]

end Parity

open Formalism.DworkPowerSeriesWeights (Integral) in
theorem integral_neg_lU {K : Type} [NormedField K] {i : PowerSeries K}
    (hi : Integral (ι := Unit) i) : Integral (ι := Unit) (-lU i) := by
  intro n
  rw [map_neg, norm_neg]
  exact hi (Finsupp.single () (n () + 1))

theorem logSigmaPullbackEven : PhOEven := by
  intro K _ _ _ s2 P l i hP hl hl1 hinv
  obtain ⟨hi, hiI, hli⟩ := hinv
  refine ⟨?_, ?_⟩
  · show constantCoeff (subst i (phO s2 P l) - phO s2 P l) = 0
    rw [map_sub, constantCoeff_psubst hi, sub_self]
  · show Formalism.DworkPowerSeriesWeights.Integral (fExp (subst i (phO s2 P l) - phO s2 P l))
    rw [fExp_phO_inv_sub s2 hP hl hl1 hi hli]
    exact integral_neg_lU hiI

theorem logSigmaOnePullbackEven : PhEEven := by
  intro K _ _ _ s2 e1 kap w l i hw hl hinv
  obtain ⟨hi, _, hli⟩ := hinv
  exact phE_inv s2 e1 kap hw hl hi hli

end Formalism.L2.Th1.B.Ph
