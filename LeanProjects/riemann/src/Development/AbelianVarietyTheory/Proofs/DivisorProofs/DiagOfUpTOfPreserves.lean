import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

private theorem eq_diagonal_of_lower_upper_zero {n : ℕ} (b : Mt n) (hlow : ∀ a c : Fin n, c < a → b a c = 0)
    (hup : ∀ a c : Fin n, a < c → b a c = 0) : b = diagonal fun a => b a a := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hup i j hij, diagonal_apply_ne _ (ne_of_lt hij)]
  · rw [diagonal_apply_eq]
  · rw [hlow i j hij, diagonal_apply_ne _ (ne_of_gt hij)]

private theorem eq_exp_arg_mul_I_of_star_mul_self_eq_one (z : ℂ) (hz : star z * z = 1) :
    z = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
  have hn : Complex.normSq z = 1 := by
    have h1 : (Complex.normSq z : ℂ) = 1 := (Complex.normSq_eq_conj_mul_self).trans hz
    exact_mod_cast h1
  have habs : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hn
    have h3 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have key := Complex.norm_mul_exp_arg_mul_I z
  rw [habs, Complex.ofReal_one, one_mul] at key
  exact key.symm

theorem diag_of_upT_of_preserves {n : ℕ} (d : Fin n → ℂ) (hd : ∀ a, d a * d a = 1) (b : Mt n) (hb : UpT b)
    (h : bᴴ * diagonal d * b = diagonal d) :
    ∃ s : Fin n → ℝ, b = diagonal fun a => Complex.exp ((s a : ℂ) * Complex.I) := by
  classical
  have hDD : diagonal d * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact hd a
  have hdne : ∀ a, d a ≠ 0 := by
    intro a h0
    have h1 := hd a
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1

  have hleft : diagonal d * bᴴ * diagonal d * b = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc bᴴ, h, hDD]
  letI : Invertible b.det := (Ne.isUnit hb.1).invertible
  letI : Invertible b := Matrix.invertibleOfDetInvertible b
  have hinv : b⁻¹ = diagonal d * bᴴ * diagonal d := Matrix.inv_eq_left_inv hleft

  have hbt : Matrix.BlockTriangular b id := fun i j hij => hb.2 i j hij
  have hbit := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have hup : ∀ a c : Fin n, a < c → b a c = 0 := by
    intro a c hac
    have h0 : b⁻¹ c a = 0 := hbit hac
    rw [hinv, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (hdne c)
      · exact star_eq_zero.1 h2
    · exact absurd h1 (hdne a)
  have hdiag := eq_diagonal_of_lower_upper_zero b hb.2 hup

  have hh := h
  rw [hdiag, Matrix.diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal] at hh
  have hu : ∀ a, star (b a a) * b a a = 1 := by
    intro a
    have h1 := congrFun (Matrix.diagonal_injective hh) a
    simp only [Pi.star_apply] at h1
    have h2 : d a * (star (b a a) * b a a) = d a * 1 := by linear_combination h1
    exact mul_left_cancel₀ (hdne a) h2
  refine ⟨fun a => Complex.arg (b a a), ?_⟩
  calc b = diagonal fun a => b a a := hdiag
    _ = _ := by
      congr 1
      funext a
      exact eq_exp_arg_mul_I_of_star_mul_self_eq_one _ (hu a)

theorem diag_of_upT_unitary : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ → ∀ b : Mt n, UpT b → x₀ * b * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm → ∃ s : Fin n → ℝ, b = diagonal fun a => Complex.exp ((s a : ℂ) * Complex.I) := by
  intro n Hm q x₀ hx b hb hu
  obtain ⟨-, hx⟩ := hx
  set d : Fin n → ℂ := fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) with hd_def
  have hd : ∀ a, d a * d a = 1 := by
    intro a
    simp only [hd_def, ReciprocityTheory.ChartRestriction.G.FD.sgn]
    split_ifs <;> norm_num
  have hdet : x₀.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hx
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at h1
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
    intro h2
    have h3 := hd a
    rw [h2, zero_mul] at h3
    exact zero_ne_one h3
  have hu' : (x₀ * b * x₀⁻¹)ᴴ * Hm * (x₀ * b * x₀⁻¹) = Hm := hu
  have hcx : x₀ * b * x₀⁻¹ * x₀ = x₀ * b := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), Matrix.mul_one]

  have key : bᴴ * diagonal d * b = diagonal d := by
    calc bᴴ * diagonal d * b = bᴴ * (x₀ᴴ * Hm * x₀) * b := by rw [hx]
      _ = (x₀ * b)ᴴ * Hm * (x₀ * b) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (x₀ * b * x₀⁻¹ * x₀)ᴴ * Hm * (x₀ * b * x₀⁻¹ * x₀) := by rw [hcx]
      _ = x₀ᴴ * ((x₀ * b * x₀⁻¹)ᴴ * Hm * (x₀ * b * x₀⁻¹)) * x₀ := by
        rw [conjTranspose_mul (x₀ * b * x₀⁻¹) x₀]; simp only [Matrix.mul_assoc]
      _ = diagonal d := by rw [hu', hx]
  exact diag_of_upT_of_preserves d hd b hb key

end GlobalTheory.HolDict
