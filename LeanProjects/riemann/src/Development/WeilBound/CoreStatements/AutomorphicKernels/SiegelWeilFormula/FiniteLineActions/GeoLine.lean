import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoRot
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.DZMulDZInv

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem cw_line' (w : InfinitePlace F) (P Q : Mx F E d.m d.n) :
    d.cw w (P * (incM F d.b.1.toCols₂)ᵀ + Q * (incM F d.b.1.toCols₁)ᵀ) =
      Matrix.fromCols (d.cw w Q) (d.cw w P) * (d.cw w (incM F d.b.1))ᵀ := by
  rw [cw_add', cw_mul', cw_mul', cw_transpose', cw_transpose']
  conv_rhs => rw [← Matrix.fromCols_toCols (d.cw w (incM F d.b.1)), Matrix.transpose_fromCols,
    Matrix.fromCols_mul_fromRows]
  rw [add_comm]
  rfl

theorem cw_realAd_smul' (w : InfinitePlace F) {p q : Type} (r : ℝ) (X : Matrix p q (AE F E)) :
    d.cw w (realAd F r • X) = (r : ℂ) • d.cw w X :=
  GlobalTheory.RealScalar.realAd_smul_map σ d.B.emb d.cm X r w

theorem exp_mul_re' (t : ℝ) (z : ℂ) :
    (Complex.exp (-(t * Complex.I)) * z).re = z.re * Real.cos t + z.im * Real.sin t := by
  simp only [Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [mul_zero, zero_mul, sub_zero, add_zero, mul_one, neg_zero, Real.exp_zero, one_mul,
    Real.cos_neg, Real.sin_neg]
  ring

theorem exp_mul_im' (t : ℝ) (z : ℂ) :
    (Complex.exp (-(t * Complex.I)) * z).im = z.im * Real.cos t - z.re * Real.sin t := by
  simp only [Complex.mul_im, Complex.exp_re, Complex.exp_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [mul_zero, zero_mul, sub_zero, add_zero, mul_one, neg_zero, Real.exp_zero, one_mul,
    Real.cos_neg, Real.sin_neg]
  ring

theorem finOne_smul_line' {W W' : Mx F E d.m d.n} (hW : finOne F • W = 0) (hW' : finOne F • W' = 0) (x y : ℝ) :
    finOne F • ((realAd F x • W) * (incM F d.b.1.toCols₂)ᵀ + (realAd F y • W') * (incM F d.b.1.toCols₁)ᵀ) = 0 := by
  rw [smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, smul_smul, smul_smul, mul_comm (finOne F),
    mul_comm (finOne F), ← smul_smul, ← smul_smul, hW, hW', smul_zero, smul_zero, Matrix.zero_mul,
    Matrix.zero_mul, add_zero]

theorem actB_rot_vline' (R : RD d) (t : ℝ) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (z : ℂ) :
    actB (cA σ) (rot R t) (vline R W z) = vline R W (Complex.exp (-(t * Complex.I)) * z) := by
  have htw := (exists_tw R W).choose_spec
  have hζ : R.ζ ≠ 0 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  unfold vline
  rw [exp_mul_re', exp_mul_im']
  have hact : ∀ v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E), actB (cA σ) (rot R t) v = v * (mat2 (rot R t))ᵀ :=
    fun v => rfl
  rw [hact]
  refine Place.cw_ext (d := d) (fun w => ?_) ?_
  · rw [cw_mul', cw_transpose', matrix_eq_frame_conj, cw_mul', cw_mul', cw_line', cw_line', cw_realAd_smul', cw_realAd_smul',
      cw_realAd_smul', cw_realAd_smul', show d.cw w (tw R W) = _ from htw.2 w]
    have hinv : d.cw w (incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) *
        d.cw w (incM F d.b.1) = 1 := by
      rw [← cw_mul', incM_b_inv_mul, cw_one']
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ (d.cw w (incM F d.b.1))ᵀ, ← Matrix.transpose_mul, hinv, Matrix.transpose_one, Matrix.mul_one,
      rot_cols' d.n d.m hζ (R.sg w) t z.re z.im (d.cw w W) _ (dZ_cw_rot' R t w)]
  · rw [← Matrix.smul_mul, finOne_smul_line' (W' := tw R W) hW htw.1, finOne_smul_line' (W' := tw R W) hW htw.1,
      Matrix.zero_mul]

end PositivityTheory.SiegelWeilFormula.KFP

end
