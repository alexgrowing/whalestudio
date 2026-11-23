import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.NormWth

theorem norm_core (m : ℕ) (A B p q r u d : ℝ) (hB : B ≠ 0)
    (h00 : p * p + q * q = 1) (h11 : r * r + u * u = 1) (h01 : p * r + q * u = 0)
    (hd : d = A * B * B * (p * u - q * r)) (hpos : 0 < d) :
    ‖((d : ℝ) : ℂ) ^ ((m : ℂ) / 2) *
        (((B * u : ℝ) : ℂ) + Complex.I * ((B * r : ℝ) : ℂ)) ^ (-(m : ℤ)) *
        Complex.exp (2 * Real.pi * Complex.I *
          ((((A * B * q : ℝ) : ℂ) + Complex.I * ((A * B * p : ℝ) : ℂ)) /
            (((B * u : ℝ) : ℂ) + Complex.I * ((B * r : ℝ) : ℂ))))‖ =
      |A| ^ ((m : ℝ) / 2) * Real.exp (-(2 * Real.pi * |A|)) := by
  set D : ℝ := p * u - q * r with hD
  have hD2 : D * D = 1 := by
    rw [hD]; linear_combination (r * r + u * u) * h00 + h11 - (p * r + q * u) * h01
  have hp : p = D * u := by
    rw [hD]; linear_combination (-p) * h11 + r * h01
  have hq : q = -(D * r) := by
    rw [hD]; linear_combination u * h01 - q * h11
  have hBB : 0 < B * B := mul_self_pos.2 hB
  have hAD : 0 < A * D := by
    have h : 0 < (A * D) * (B * B) := by rw [hd] at hpos; linarith [hpos, (by ring : A * B * B * D = (A * D) * (B * B))]
    by_contra hn
    nlinarith [not_lt.1 hn, hBB]
  have ht : A * D = |A| := by
    have h1 : (D - 1) * (D + 1) = 0 := by linear_combination hD2
    rcases mul_eq_zero.1 h1 with h | h
    · have hD1 : D = 1 := by linarith
      rw [hD1, mul_one] at hAD ⊢
      exact (abs_of_pos hAD).symm
    · have hD1 : D = -1 := by linarith
      rw [hD1] at hAD ⊢
      have : A < 0 := by linarith
      rw [abs_of_neg this]; ring
  set t : ℝ := |A| with htdef
  have htpos : 0 < t := ht ▸ hAD
  have hdt : d = t * (B * B) := by rw [hd, ← ht]; ring
  set z : ℂ := (u : ℂ) + (r : ℂ) * Complex.I with hz
  have hz1 : ‖z‖ = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, hz, Complex.normSq_add_mul_I]; linarith [h11, sq u, sq r]
    have h0 := norm_nonneg z
    nlinarith
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  have hBc : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hB
  have hx : ((B * u : ℝ) : ℂ) + Complex.I * ((B * r : ℝ) : ℂ) = (B : ℂ) * z := by
    rw [hz]; push_cast; ring
  have hy : ((A * B * q : ℝ) : ℂ) + Complex.I * ((A * B * p : ℝ) : ℂ) =
      (B : ℂ) * z * (Complex.I * (t : ℂ)) := by
    rw [hz, ← ht, hp, hq]
    push_cast
    linear_combination (-((A : ℂ) * B * D * r)) * Complex.I_sq
  have hexp : 2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (t : ℂ)) =
      ((-(2 * Real.pi * t) : ℝ) : ℂ) := by
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * t) * Complex.I_sq
  rw [hx, hy, mul_div_cancel_left₀ _ (mul_ne_zero hBc hz0), hexp, norm_mul, norm_mul,
    ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_zpow, norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hm : ((m : ℂ) / 2) = (((m : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hm, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.ofReal_re, hdt,
    Real.mul_rpow htpos.le hBB.le]
  have hab : 0 < |B| := abs_pos.2 hB
  have hB2 : (B * B) ^ ((m : ℝ) / 2) = |B| ^ m := by
    rw [← abs_mul_self B, abs_mul, ← sq, ← Real.rpow_natCast |B| 2, ← Real.rpow_mul hab.le,
      ← Real.rpow_natCast |B| m]
    congr 1
    push_cast
    ring
  rw [hB2, _root_.zpow_neg, zpow_natCast]
  have : |B| ^ m ≠ 0 := (pow_pos hab m).ne'
  field_simp

theorem norm_WthR_iwasawa_le : ∀ (n : ℤ) (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 →
    ‖GL2LocalData.WthR n (dg2 (a * b) b * k)‖ ≤
      |(a : ℝ)| ^ (((n.natAbs + 1 : ℕ) : ℝ) / 2) * Real.exp (-(2 * Real.pi * |(a : ℝ)|)) := by
  intro n a b k hk
  have h00 : k.val 0 0 * k.val 0 0 + k.val 0 1 * k.val 0 1 = 1 := by
    have := congrFun (congrFun hk 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : k.val 1 0 * k.val 1 0 + k.val 1 1 * k.val 1 1 = 1 := by
    have := congrFun (congrFun hk 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : k.val 0 0 * k.val 1 0 + k.val 0 1 * k.val 1 1 = 0 := by
    have := congrFun (congrFun hk 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e00 : (dg2 (a * b) b * k).val 0 0 = (a : ℝ) * b * k.val 0 0 := by
    simp [dg2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (dg2 (a * b) b * k).val 0 1 = (a : ℝ) * b * k.val 0 1 := by
    simp [dg2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (dg2 (a * b) b * k).val 1 0 = (b : ℝ) * k.val 1 0 := by
    simp [dg2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (dg2 (a * b) b * k).val 1 1 = (b : ℝ) * k.val 1 1 := by
    simp [dg2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : ((dg2 (a * b) b * k).val).det =
      (a : ℝ) * b * b * (k.val 0 0 * k.val 1 1 - k.val 0 1 * k.val 1 0) := by
    rw [Matrix.det_fin_two, e00, e01, e10, e11]; ring
  by_cases hd : 0 < ((dg2 (a * b) b * k).val).det
  · have h := norm_core (n.natAbs + 1) a b (k.val 0 0) (k.val 0 1) (k.val 1 0) (k.val 1 1)
      _ b.ne_zero h00 h11 h01 hdet hd
    unfold GL2LocalData.WthR
    rw [if_pos hd, e00, e01, e10, e11]
    exact h.le
  · have h0 : GL2LocalData.WthR n (dg2 (a * b) b * k) = 0 := by
      unfold GL2LocalData.WthR
      rw [if_neg hd]
    rw [h0, norm_zero]
    positivity

end GlobalTheory.CompanionTheory.GL2Factorization.NormWth
