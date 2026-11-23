import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariant
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.ThetaShift

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

variable {D : D7} {N N' : ℕ}

theorem Hf_nsmul_left (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T (n • x) y = (n : ℂ) * Hf D T x y := by
  induction n with
  | zero => simp [Hf]
  | succ n ih => rw [succ_nsmul, Hf_add_left, ih]; push_cast; ring

theorem Hf_nsmul_right (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T x (n • y) = (n : ℂ) * Hf D T x y := by
  induction n with
  | zero => simp [Hf]
  | succ n ih => rw [succ_nsmul, Hf_add_right, ih]; push_cast; ring

theorem qH_nsmul (T : Tor D) (n : ℕ) (x : VC D N N') :
    qH D T (n • x) = (n : ℝ) ^ 2 * qH D T x := by
  unfold qH
  rw [Hf_nsmul_left, Hf_nsmul_right, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  ring

theorem qH_int (T : Tor D) {Λ : AddSubgroup (VC D N N')} (hI : HfInt T Λ) {w : VC D N N'} (hw : w ∈ Λ) :
    ∃ m : ℤ, qH D T w = m ∧ al D T w = (-1 : ℂ) ^ m := by
  obtain ⟨m, h1, h2⟩ := self_int T hI hw
  have hs := sqrt_d_pos D
  refine ⟨m, ?_, ?_⟩
  · unfold qH
    rw [h1]
    field_simp
  · unfold al
    rw [h2]

theorem qH_add (T : Tor D) (x w : VC D N N') :
    qH D T (x + w) = qH D T x + qH D T w + Real.sqrt D.host.d * (Hf D T x w).re := by
  unfold qH
  rw [Hf_add_left, Hf_add_right, Hf_add_right, Complex.add_re, Complex.add_re, Complex.add_re,
    Hf_re_swap T x w]
  ring

theorem wPh_shift (T : Tor D) {p : ℕ} (hp : p.Prime) {x y : VC D N N'} {k : ℕ} {M n : ℤ}
    (hM : (p : ℝ) ^ k * qH D T x = M) (hy : qH D T y = qH D T x + n) :
    wPh D T p y = wPh D T p x * (-1 : ℂ) ^ n := by
  by_cases h2 : p = 2
  · unfold wPh
    rw [if_pos h2, if_pos h2, hy, ← GlobalTheory.GalThetaSign.exp_int_pi, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · have hM' : (p : ℝ) ^ k * qH D T y = ((M + ((p ^ k : ℕ) : ℤ) * n : ℤ) : ℝ) := by
      rw [hy, mul_add, hM]
      push_cast
      ring
    rw [GlobalTheory.GalThetaSign.wPh_eq D T x hp h2 hM, GlobalTheory.GalThetaSign.wPh_eq D T y hp h2 hM',
      zpow_add₀ (by norm_num), zpow_mul, zpow_natCast,
      ((hp.odd_of_ne_two h2).pow : Odd (p ^ k)).neg_one_pow]

theorem Wop_add_lattice : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (Λ : AddSubgroup (VC D N N')) (p : ℕ), p.Prime → Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T Λ → ∀ G ∈ ThSp D T Λ, ∀ x w : VC D N N', w ∈ Λ → (∃ k : ℕ, p ^ k • x ∈ Λ) → (∃ a b : ℤ, Even (a - b) ∧ Hf D T x w = (((a : ℝ) / Real.sqrt D.host.d : ℝ) : ℂ) + (b : ℂ) * Complex.I) → Wop D T p (x + w) G = Wop D T p x G := by
  intro D T N N' Λ p hp hI G hG x w hw ⟨k, hk⟩ ⟨a, b, hab, h⟩
  have hs := sqrt_d_pos D
  obtain ⟨m, hm, hal⟩ := qH_int T hI hw
  obtain ⟨M, hM, -⟩ := qH_int T hI hk
  have hM' : (p : ℝ) ^ (k * 2) * qH D T x = M := by
    rw [← hM, qH_nsmul, pow_mul]
    push_cast
    ring
  have hre : (Hf D T x w).re = a / Real.sqrt D.host.d := by rw [h]; simp
  have him : (Hf D T x w).im = b := by rw [h]; simp
  have hq : qH D T (x + w) = qH D T x + ((m + a : ℤ) : ℝ) := by
    rw [qH_add, hm, hre]
    push_cast
    field_simp
    ring
  have hph := wPh_shift T hp hM' hq
  funext z
  have hU : U D T x G z = al D T w * cf T x w * U D T (x + w) G z := by
    conv_lhs => rw [← fix_eq T hG hw]
    rw [U_smul, U_U]; ring
  have hsgn : (-1 : ℂ) ^ (m + a) = (-1 : ℂ) ^ m * (-1 : ℂ) ^ (-b) := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    apply neg_one_zpow_congr
    have : m + a - (m + -b) = (a - b) + 2 * b := by ring
    rw [this]
    exact hab.add (even_two_mul b)
  unfold Wop
  rw [hU, hph, hal, cf_int T x w b him, hsgn]
  ring

end GlobalTheory.ThetaShift
