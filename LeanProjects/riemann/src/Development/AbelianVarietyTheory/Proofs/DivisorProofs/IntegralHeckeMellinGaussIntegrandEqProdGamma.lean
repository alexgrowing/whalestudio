import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaIntegralExpSubstitutionRealLineStatement
open NumberField MeasureTheory

noncomputable section
namespace GlobalTheory.HeckeMellinProd

theorem hmon_real_mul (n : ℤ) (c : ℝ) (z : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((c : ℂ) * z) = (c : ℂ) ^ n.natAbs * GlobalTheory.HeckeTheta.hmon n z := by
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · rw [map_mul, Complex.conj_ofReal, mul_pow]; congr 2; omega
  · rw [mul_pow]; congr 2; omega

def fac (w : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))

theorem coord (n : ℤ) (s : ℂ) (v : ℂ) (y : ℝ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * v) *
      Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 : ℝ) : ℂ) * Complex.exp (s * (y : ℂ)) =
    GlobalTheory.HeckeTheta.hmon n v * fac (s + ((|n| : ℤ) : ℂ) / 2) (‖v‖ ^ 2) y := by
  rw [hmon_real_mul, fac]
  have h1 : ((Real.exp (y / 2) : ℝ) : ℂ) ^ n.natAbs = Complex.exp ((n.natAbs : ℂ) * (y / 2)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]; push_cast; rfl
  have h2 : ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 = Real.exp y * ‖v‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
      ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have h3 : ((|n| : ℤ) : ℂ) = (n.natAbs : ℂ) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  rw [h1, h2, h3]
  have e1 : ((-2 * Real.pi * (Real.exp y * ‖v‖ ^ 2) : ℝ) : ℂ) = -(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1]
  calc _ = GlobalTheory.HeckeTheta.hmon n v * (Complex.exp ((n.natAbs : ℂ) * (y / 2)) * Complex.exp (s * (y : ℂ))) *
        Complex.exp (-(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [← Complex.exp_add, mul_assoc]; congr 3; ring

theorem term_eq (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) :
    GlobalTheory.HeckeMellin.term n s v y =
      ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) (y i) := by
  unfold GlobalTheory.HeckeMellin.term GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeTheta.dil
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact coord (n i) s (v i) (y i)

theorem norm_fac (w : ℂ) (r : ℝ) (t : ℝ) :
    ‖fac w r t‖ = Real.exp (w.re * t) * Real.exp (-(2 * Real.pi * r * Real.exp t)) := by
  rw [fac, norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 2
  · simp

theorem ofReal_norm_fac (w : ℂ) (r : ℝ) (t : ℝ) :
    ((‖fac w r t‖ : ℝ) : ℂ) = fac (w.re : ℂ) r t := by
  rw [norm_fac, fac]; push_cast; rfl

end GlobalTheory.HeckeMellinProd

namespace GlobalTheory.HeckeMellinProd

theorem fac_int (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    Integrable (fac w r) ∧ ∫ t, fac w r t = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) :=
  GlobalTheory.T.gamma_integral_exp_substitution_real_line r hr w hw

theorem norm_fac_int (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    ∫ t, ‖fac w r t‖ = Real.Gamma w.re * (2 * Real.pi * r) ^ (-w.re) := by
  have h := (fac_int (w.re : ℂ) (by simpa using hw) r hr).2
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [ofReal_norm_fac]
  rw [h, Complex.ofReal_mul (Real.Gamma w.re), Complex.ofReal_cpow (by positivity), ← Complex.Gamma_ofReal]
  push_cast; ring_nf

theorem mellin_prod : ∀ (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ v : I → ℂ, (∀ i, v i ≠ 0) → Integrable (GlobalTheory.HeckeMellin.term n s v) ∧ ∫ y, GlobalTheory.HeckeMellin.term n s v y = ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) * ((2 * Real.pi * ‖v i‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s v y‖ = ∏ i, ‖v i‖ ^ (n i).natAbs * Real.Gamma (s.re + (|n i| : ℝ) / 2) * (2 * Real.pi * ‖v i‖ ^ 2) ^ (-(s.re + (|n i| : ℝ) / 2)) := by
  intro I _ n s hs v hv
  have hw : ∀ i, 0 < (s + ((|n i| : ℤ) : ℂ) / 2).re := fun i => by
    have : (0 : ℝ) ≤ |((n i : ℤ) : ℝ)| := abs_nonneg _
    simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
    norm_num
    positivity
  have hr : ∀ i, 0 < ‖v i‖ ^ 2 := fun i => pow_pos (norm_pos_iff.2 (hv i)) 2
  have hwre : ∀ i, (s + ((|n i| : ℤ) : ℂ) / 2).re = s.re + (|n i| : ℝ) / 2 := fun i => by
    simp [Complex.add_re, Complex.div_re]
  set g : I → ℝ → ℂ := fun i t => GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) t with hg
  have hterm : GlobalTheory.HeckeMellin.term n s v = fun y => ∏ i, g i (y i) := funext (term_eq I n s v)
  have hgi : ∀ i, Integrable (g i) := fun i => ((fac_int _ (hw i) _ (hr i)).1.const_mul _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hterm]; exact Integrable.fintype_prod (μ := fun _ => volume) hgi
  · rw [hterm, integral_fintype_prod_volume_eq_prod g]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hg]
    rw [integral_const_mul, (fac_int _ (hw i) _ (hr i)).2]; ring
  · have hn : (fun y => ‖GlobalTheory.HeckeMellin.term n s v y‖) = fun y => ∏ i, (fun i t => ‖g i t‖) i (y i) := by
      rw [hterm]; funext y; exact norm_prod _ _
    rw [hn, integral_fintype_prod_volume_eq_prod (fun i t => ‖g i t‖)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hg, norm_mul]
    rw [integral_const_mul, norm_fac_int _ (hw i) _ (hr i), GlobalTheory.HeckeTheta.norm_hmon, hwre]; ring

end GlobalTheory.HeckeMellinProd
