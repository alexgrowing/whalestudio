import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.GalTheta.Period

variable (D : D7) (T : Tor D) {N N' : ℕ}

theorem Hf_two_mul (m : ℕ) (y l : VC D N N') : Hf D T y ((2 * m) • l) = 2 * Hf D T (m • y) l := by
  rw [Hf_nsmul_right, Hf_nsmul_left]; push_cast; ring

theorem qH_add (a b : VC D N N') :
    qH D T (a + b) = qH D T a + qH D T b + Real.sqrt D.host.d * (Hf D T a b).re := by
  simp only [qH, Hf_add_left, Hf_add_right, Complex.add_re, Hf_re_swap D T a b]
  ring

theorem qH_nsmul (n : ℕ) (a : VC D N N') : qH D T (n • a) = (n : ℝ) ^ 2 * qH D T a := by
  simp only [qH, Hf_nsmul_left, Hf_nsmul_right]
  have : ((n : ℂ) * ((n : ℂ) * Hf D T a a)).re = (n : ℝ) ^ 2 * (Hf D T a a).re := by
    simp; ring
  rw [this]; ring

theorem exp_even (r : ℝ) (m : ℤ) (h : r = 2 * m) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (r : ℂ)) = 1 := by
  rw [h, Complex.exp_eq_one_iff]
  exact ⟨-m, by push_cast; ring⟩

theorem period (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N'))
    (hIm : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) (hq : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (e₀ : VC D N N' → ℂ) (x : VC D N N') (m₀ : ℕ)
    (he : e₀ ∈ ThSp D T A) (hx : m₀ • x ∈ A) (ht : ∀ i, m₀ • t i ∈ A) (l : VC D N N') (hl : l ∈ A) :
    U D T (x + (2 * m₀) • l) (comb D T c t e₀) = U D T x (comb D T c t e₀) ∧
      wdPh D T (x + (2 * m₀) • l) = wdPh D T x := by
  obtain ⟨ql, hql⟩ := hq l hl
  have hqμ : qH D T ((2 * m₀) • l) = ((2 * (2 * (m₀ : ℤ) ^ 2 * ql) : ℤ) : ℝ) := by
    rw [qH_nsmul, hql]; push_cast; ring
  have hμ : U D T ((2 * m₀) • l) e₀ = e₀ := by
    funext z
    have h := he.2 _ (A.nsmul_mem hl (2 * m₀)) z
    have hal : al D T ((2 * m₀) • l) = 1 := by
      change (-1 : ℂ) ^ (round (qH D T ((2 * m₀) • l))) = 1
      rw [hqμ, round_intCast, zpow_mul]
      norm_num
    rwa [hal, one_mul] at h
  have hev : ∀ y : VC D N N', m₀ • y ∈ A → ∃ m : ℤ, (Hf D T y ((2 * m₀) • l)).im = 2 * m := by
    intro y hy
    obtain ⟨m, hm⟩ := hIm _ hy _ hl
    exact ⟨m, by rw [Hf_two_mul, ← hm]; simp⟩
  refine ⟨?_, ?_⟩
  · have key : ∀ (s : VC D N N'), m₀ • s ∈ A → ∀ z,
        U D T (x + (2 * m₀) • l) (U D T s e₀) z = U D T x (U D T s e₀) z := by
      intro s hs z
      have h1 : U D T (x + s) e₀ z = U D T (x + (2 * m₀) • l + s) e₀ z := by
        obtain ⟨m, hm⟩ := hev (x + s) (by rw [smul_add]; exact A.add_mem hx hs)
        conv_lhs => rw [← hμ]
        rw [U_U, exp_even _ m hm, one_mul, add_right_comm]
      obtain ⟨m, hm⟩ := hev s hs
      have h2 : (Hf D T ((2 * m₀) • l) s).im = 2 * ((-m : ℤ) : ℝ) := by
        rw [Hf_im_swap, hm]; push_cast; ring
      rw [U_U, U_U, h1, Hf_add_left, Complex.add_im, Complex.ofReal_add, mul_add, Complex.exp_add,
        exp_even _ _ h2, mul_one]
    have h : ∀ y z, U D T y (comb D T c t e₀) z = ∑ j, c j * U D T y (U D T (t j) e₀) z := by
      intro y z
      have := U_sum D T Finset.univ y (fun j w => c j * U D T (t j) e₀ w) z
      simp only [U_mul] at this
      exact this
    funext z
    rw [h, h]
    exact Finset.sum_congr rfl fun j _ => by rw [key _ (ht j)]
  · obtain ⟨a, ha⟩ := hq _ hx
    obtain ⟨b, hb⟩ := hq _ (A.add_mem hx hl)
    have h1 := qH_add D T (m₀ • x) l
    have h2 := qH_add D T x ((2 * m₀) • l)
    have h3 : (Hf D T x ((2 * m₀) • l)).re = 2 * (Hf D T (m₀ • x) l).re := by
      rw [Hf_two_mul]; simp
    have h4 : qH D T (x + (2 * m₀) • l) / 2 =
        qH D T x / 2 + ((2 * (m₀ : ℤ) ^ 2 * ql + (b - a - ql) : ℤ) : ℝ) := by
      rw [h2, hqμ, h3]
      rw [ha, hb, hql] at h1
      push_cast
      linarith
    unfold wdPh ee
    rw [h4, Complex.ofReal_add, mul_add, Complex.exp_add, Complex.ofReal_intCast,
      mul_comm _ ((_ : ℤ) : ℂ), Complex.exp_int_mul_two_pi_mul_I, mul_one]

end GlobalTheory.GalTheta.Period
