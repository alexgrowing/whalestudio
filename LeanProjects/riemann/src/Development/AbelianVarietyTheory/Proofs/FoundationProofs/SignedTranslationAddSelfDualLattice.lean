import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem al_add (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N'))
    (h1 : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) (h2 : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (h3 : ∀ x ∈ A, w0 D • x ∈ A) : ∀ x ∈ A, ∀ y ∈ A, al D T (x + y) =
      al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) := by
  intro x hx y hy
  obtain ⟨a, ha⟩ := h2 x hx
  obtain ⟨c, hc⟩ := h2 y hy
  obtain ⟨b, hb⟩ := h1 x hx y hy
  obtain ⟨k, hk⟩ := h1 _ (h3 x hx) y hy
  have hal : ∀ z : VC D N N', ∀ m : ℤ, qH D T z = m → al D T z = (-1 : ℂ) ^ m := by
    intro z m hm
    have e : al D T z = (-1 : ℂ) ^ (round (qH D T z)) := rfl
    rw [e, hm, round_intCast]
  have hk' : Real.sqrt D.host.d * (Hf D T x y).re = 2 * k - b := by
    rw [Hf_smul_left] at hk
    rw [← hk, ← hb]
    simp [w0, Complex.mul_im]
    ring
  have hs : qH D T (x + y) = ((a + c + (2 * k - b) : ℤ) : ℝ) := by
    push_cast
    rw [← ha, ← hc, ← hk']
    simp only [qH, Hf_add_left, Hf_add_right, Complex.add_re, Hf_re_swap D T x y]
    ring
  have he : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) = (-1 : ℂ) ^ (-b) := by
    rw [hb, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  rw [hal _ _ hs, hal _ _ ha, hal _ _ hc, he, sub_eq_add_neg, zpow_add₀ hn, zpow_add₀ hn, zpow_add₀ hn,
    zpow_mul]
  simp

end GlobalTheory.GalTheta
