import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FourDepthLtConductorOfBounds

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

open Classical in

def RestOddTops : Prop :=
  ∀ (n' : ℕ) (TT : Finset (Fin n')), 2 ≤ numSeg TT → ∀ f : Fin n' → Fin n' → ℕ → ℝ,
    ∑ j : Fin (numSeg TT), ∑ i : Fin (segS TT j), f (segPos TT j i) (segStart TT j) ((segDists TT j).get i) =
      ∑ y ∈ TT.filter (fun y => ¬ IsTypeV y), f y (yPrev TT y) (dPrev TT y)

theorem tle_abs (Ct C N N1 p k Q L ar a' b' La La' ccl cS n' S S' : ℝ) (hCt : 0 < Ct) (hC : 4 * Ct + 4 ≤ C)
    (hN : 1 ≤ N) (hN1 : 1 ≤ N1) (hp : 0 < p) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hL : 0 ≤ L) (har : 0 ≤ ar)
    (ha0 : 0 ≤ a') (ha : a' ≤ 2 * ar) (hb : 0 < b') (hLa : 0 ≤ La) (hLa0 : 0 ≤ La') (hLa' : La' ≤ 2 * La)
    (hccl : 0 ≤ ccl) (hcS : 0 ≤ cS) (hn' : 0 ≤ n') (hS : S' ≤ S + N * ccl) :
    (S' + Ct * N * (a' / p ^ 2 + b' / p + La' * a' / (p * k) + La' * b' / k + k * Q +
        Q * (cS + 2 * N * ccl + 2 * n' * ccl))) + N * (La' * b' / k) + 1 + 2 * n' * ccl ≤
      S + C * N * N1 * (ar / p ^ 2 + b' / p + La * ar / (p * k) + La * b' / k) +
        C * N * (Q * (cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl) + k * Q + k * L + ccl) + 2 * n' * ccl := by
  have hN0 : 0 ≤ N := by linarith
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hCN1 : C ≤ C * N1 := by nlinarith
  have hp2 : 0 < p ^ 2 := by positivity
  have hA : a' / p ^ 2 ≤ 2 * (ar / p ^ 2) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right ha hp2.le
  have hA0 : 0 ≤ ar / p ^ 2 := by positivity
  have hB0 : 0 ≤ b' / p := by positivity
  have hE : La' * a' / (p * k) ≤ 4 * (La * ar / (p * k)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul hLa' ha ha0 (by linarith : (0 : ℝ) ≤ 2 * La)
    linarith
  have hE0 : 0 ≤ La * ar / (p * k) := by positivity
  have hF : La' * b' / k ≤ 2 * (La * b' / k) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hk0.le
    nlinarith
  have hF0 : 0 ≤ La * b' / k := by positivity
  have hF'0 : 0 ≤ La' * b' / k := by positivity
  have t1 : Ct * N * (a' / p ^ 2) ≤ C * N * N1 * (ar / p ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hA (mul_nonneg hCt.le hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * Ct ≤ C * N1) (mul_nonneg hN0 hA0)
    nlinarith
  have t2 : Ct * N * (b' / p) ≤ C * N * N1 * (b' / p) := by
    have h2 := mul_le_mul_of_nonneg_right (by linarith : Ct ≤ C * N1) (mul_nonneg hN0 hB0)
    nlinarith
  have t3 : Ct * N * (La' * a' / (p * k)) ≤ C * N * N1 * (La * ar / (p * k)) := by
    have h1 := mul_le_mul_of_nonneg_left hE (mul_nonneg hCt.le hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 4 * Ct ≤ C * N1) (mul_nonneg hN0 hE0)
    nlinarith
  have t4 : Ct * N * (La' * b' / k) + N * (La' * b' / k) ≤ C * N * N1 * (La * b' / k) := by
    have h1 := mul_le_mul_of_nonneg_left hF (mul_nonneg (by linarith : (0 : ℝ) ≤ Ct + 1) hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * Ct + 2 ≤ C * N1) (mul_nonneg hN0 hF0)
    nlinarith
  have hNkQ : 1 ≤ N * k * Q := by
    have := one_le_mul_of_one_le_of_one_le hN hk
    exact one_le_mul_of_one_le_of_one_le this hQ
  have t5 : Ct * N * (k * Q) + 1 ≤ C * N * (k * Q) := by
    have h2 := mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ C - Ct) (by linarith : (0 : ℝ) ≤ N * k * Q)
    nlinarith
  have hX0 : 0 ≤ cS + 2 * N * ccl + 2 * n' * ccl := by positivity
  have hXY : cS + 2 * N * ccl + 2 * n' * ccl ≤ cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl := by
    have : 0 ≤ C * N * k * L := by positivity
    have : 0 ≤ N * ccl := by positivity
    linarith
  have t6 : Ct * N * (Q * (cS + 2 * N * ccl + 2 * n' * ccl)) ≤
      C * N * (Q * (cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl)) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hN0)
      (mul_le_mul_of_nonneg_left hXY hQ0) (mul_nonneg hQ0 hX0) (mul_nonneg hC0 hN0)
  have t7 : N * ccl ≤ C * N * (k * L + ccl) := by
    have : 0 ≤ C * N * (k * L) := by positivity
    have h2 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C) (mul_nonneg hN0 hccl)
    linarith
  linarith [t1, t2, t3, t4, t5, t6, t7]

theorem initial_level_formula (K : Cst) (X : Dat) (A B : X.TT → ℕ) :
    X.t0 K A B = (∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        min ((ex B (segPos X.TT j i) : ℕ) : ℝ)
          (((ex A (segStart X.TT j) : ℕ) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i))) +
      K.Ct * X.N * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.a * X.a / (X.p * X.k) +
        LaI K.C₀ X.N₁ X.a * X.b' / X.k + X.k * (X.p : ℝ) ^ X.G' +
        (X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + 2 * X.N * X.ccl + 2 * X.n' * X.ccl)) := by
  unfold Dat.t0 t0I t0G4 Dat.c4 Dat.N Dat.k
  push_cast
  ring

end Formalism.MainNotions.flipOneThree.Pf

end
