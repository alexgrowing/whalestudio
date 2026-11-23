import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtEvalCurve

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, sgn ε a * (star (x a i) * x a j) := by
  simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, eval_X, Finset.sum_filter, if_true]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases h : ε a <;> simp [sgn, h]

theorem gramX_scal (ε : Fin m → Bool) (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) :
    gramX ε (scal α x) = diagonal (fun j => (α j : ℂ)) * gramX ε x * diagonal (fun j => (α j : ℂ)) := by
  ext i j
  simp only [gramX_apply, mul_diagonal, diagonal_mul, scal, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

theorem gramX_herm (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x)ᴴ = gramX ε x := by
  ext i j
  simp only [conjTranspose_apply, gramX_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases h : ε a <;> simp [sgn, h, mul_comm]

theorem trace_im (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) :
    ((b * gramX ε x).trace).im = 0 := by
  have hG := gramX_herm ε x
  have h1 : star ((b * gramX ε x).trace) = (b * gramX ε x).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hG, hb.eq, trace_mul_comm]
  have h2 := congrArg Complex.im h1
  simp only [Complex.star_def, Complex.conj_im] at h2
  linarith

theorem norm_phase (t : ℝ) (z : ℂ) (hz : z.im = 0) : ‖Complex.exp (Complex.I * t * z)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, hz]

theorem trace_scal (ε : Fin m → Bool) (X : Fin n → ℝ) (h : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    (bS X h b * gramX ε (scal (aH X h) y)).trace = (b * gramX ε y).trace := by
  rw [gramX_scal]
  simp only [bS]
  set A : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((Real.exp (-(h * X j)) : ℝ) : ℂ)
  set B : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((aH X h j : ℝ) : ℂ)
  have hAB : A * B = 1 := by
    simp only [A, B, diagonal_mul_diagonal, aH]
    rw [← diagonal_one]
    congr 1
    funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hBA : B * A = 1 := by
    simp only [A, B, diagonal_mul_diagonal, aH]
    rw [← diagonal_one]
    congr 1
    funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  rw [show A * b * A * (B * gramX ε y * B) = A * (b * ((A * B) * gramX ε y * B)) by
    simp only [mul_assoc], hAB, one_mul, trace_mul_comm,
    show b * (gramX ε y * B) * A = b * gramX ε y * (B * A) by simp only [mul_assoc], hBA, mul_one]

theorem ept_true (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ept v (a, j, true) = star (v a j) := rfl
theorem ept_false (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ept v (a, j, false) = v a j := rfl

theorem evX_dil (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (v : Fin m → Fin n → ℂ) :
    evX (dil c X Q) v = ((m : ℂ) * ∑ j, (X j : ℂ)) * evX Q v +
      ∑ k, eval (ept v) (pderiv k Q) * ((X k.2.1 : ℂ) * ept v k) -
      (c : ℂ) * (∑ a, ∑ j, 2 * (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * evX Q v := by
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have key : ∀ a b c d a' b' c' d' : ℂ, a = a' → b = c' → c = b' → d = d' →
      a + (b + c - d) = a' + (b' + c') - d' := by
    intros
    subst_vars
    ring
  show eval (ept v) (dil c X Q) = ((m : ℂ) * ∑ j, (X j : ℂ)) * eval (ept v) Q +
      ∑ k, eval (ept v) (pderiv k Q) * ((X k.2.1 : ℂ) * ept v k) -
      (c : ℂ) * (∑ a, ∑ j, 2 * (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * eval (ept v) Q
  simp only [dil, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, MvPolynomial.smul_eq_C_mul, nsmul_eq_mul, map_sum, map_add, map_sub,
    map_mul, eval_X, eval_C, map_natCast, ept_true, ept_false, Derivation.coeFn_coe, hn]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ept_true, ept_false]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m))), Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  apply key
  · exact Finset.sum_congr rfl (fun _ _ => by ring)
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

end PositivityTheory.Rg.Sw.AbsSt.DF
