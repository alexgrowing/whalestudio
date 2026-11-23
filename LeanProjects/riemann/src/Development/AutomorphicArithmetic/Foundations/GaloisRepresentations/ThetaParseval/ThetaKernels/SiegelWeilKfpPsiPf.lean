import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FrameArchimedeanPairing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpGeo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GramSuppCmpK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLrho

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Psi
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem psi_tt_arch_k (M : Mx F E d.n d.n) (hM : finOne F • M = 0) :
    d.B.ψ (d.tt M) = Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ w, 2 * ((d.cw w M).trace).re : ℝ) : ℂ)) := by
  have hf : finOne F • M.trace = 0 := by rw [← Matrix.trace_smul, hM, Matrix.trace_zero]
  have hf' : finOne F * d.tt M = 0 := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt
    rw [← smul_eq_mul, ← LinearMap.map_smul, hf, map_zero]
  rw [d.std.2.2 _ (Place.at_of_finOne hf'), Dense.trace_evI d.cm.1]
  congr 3
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt
  rw [Dense.ext_trace d.cm (d.B.emb w), Dense.piInf_cA d.cm]
  have : piInf (d.B.emb w) M.trace = (d.cw w M).trace := by simp [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, map_sum]
  rw [this, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring
theorem cw_realAd_k (w : InfinitePlace F) {p q : Type} (t : ℝ) (Y : Matrix p q (AE F E)) :
    d.cw w (realAd F t • Y) = (t : ℂ) • d.cw w Y := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, GlobalTheory.RealScalar.piInf_realAd_smul]
theorem tw_spec_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) :
    finOne F • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W = 0 ∧ ∀ w, d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W :=
  (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_tw_k R W).choose_spec
theorem sg_sq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : ((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]
theorem cw_gram_tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) (w : InfinitePlace F) :
    d.cw w (d.gram (realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) X) =
      (-(t : ℂ)) • ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w X)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.cw_realAd_k, (_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.tw_spec_k R W).2, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_loc_k R w W, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_loc_k R w X]
  have h3 : ((R.fr w).1 * (Matrix.of (R.loc w X)).map star).map star = (R.fr w).1.map star * Matrix.of (R.loc w X) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h3]
  have hz := _root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R
  have e := _root_.PositivityTheory.SiegelWeilFormula.KW.frJ_k R w
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.transpose_mul]
  calc _ = ((t : ℂ) * (-(((R.sg w : ℤ) : ℂ) * R.ζ))) • (((Matrix.of (R.loc w W)).map star)ᵀ *
        ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of (R.loc w X)) := by
        rw [smul_smul]; simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
        have h4 : ((Matrix.of (R.loc w W)).map star)ᵀ = (Matrix.of (R.loc w W))ᴴ := rfl
        rw [h4]
        congr 1
        field_simp
        linear_combination (-(t : ℂ)) * _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.sg_sq_k R w
theorem re_trace_loc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (W X : Mx F E d.m d.n) :
    (((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w X)).trace).re =
      ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re]
theorem inner_arc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W X : Mx F E d.m d.n) :
    ⟪_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X⟫_ℝ =
      ∑ w, ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, PiLp.inner_apply, EuclideanSpace.equiv, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp
  ring
theorem fin_gram_tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) :
    finOne F • d.gram (realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) X = 0 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, smul_comm, (_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.tw_spec_k R W).1]
  simp
theorem spf_eq_k (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d x y = Algebra.trace (AF F) (AE F E)
      (-(xᵀ * incM F d.A.J * y.map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k symp
  rw [hTens_trace, neg_one_mul]
theorem trace_evI_trace_k (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w, 2 * (piInf (d.B.emb w) z).re := by
  rw [Dense.trace_evI d.cm.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Dense.ext_trace d.cm (d.B.emb w), Dense.piInf_cA d.cm, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring
theorem psi_neg_half_trace_k (z : AE F E) (hz : finOne F • z = 0) :
    d.B.ψ (-(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) z)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((-(∑ w, (piInf (d.B.emb w) z).re) : ℝ) : ℂ)) := by
  have hf : finOne F * Algebra.trace (AF F) (AE F E) z = 0 := by
    rw [← smul_eq_mul, ← LinearMap.map_smul, hz, map_zero]
  have hf' : finOne F * -(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) z) = 0 := by
    rw [mul_neg, mul_left_comm, hf, mul_zero, neg_zero]
  rw [d.std.2.2 _ (Place.at_of_finOne hf')]
  congr 3
  have e : evI F (-(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) z)) =
      -(algebraMap ℝ (mixedEmbedding.mixedSpace F) (⅟2) * evI F (Algebra.trace (AF F) (AE F E) z)) := by
    rw [← evI_half, ← Dense.evI_mul]
    exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) _
  rw [e, map_neg, ← Algebra.smul_def, LinearMap.map_smul, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.trace_evI_trace_k, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [invOf_eq_inv]
  ring
theorem frame_hermForm_real_sign (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) :
    ((d.b.1.toCols₂).map (d.B.emb w).1)ᵀ * (dbl d.Y.J).map (d.B.emb w).1 *
      ((d.b.1.toCols₁).map (d.B.emb w).1).map star = (((R.ε : ℤ) : ℂ)) • 1 := by
  have h := congrArg (fun x => x.map (d.B.emb w).1) R.hε
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  have cst : (d.b.1.map σ).map (d.B.emb w).1 = (d.b.1.map (d.B.emb w).1).map star := by
    ext i j; exact d.cm.2.2.2 (d.B.emb w).1 (d.b.1 i j)
  rw [cst] at h
  ext i j
  have := congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
  simpa [Matrix.mul_apply, Matrix.toCols₁, Matrix.toCols₂, Matrix.one_apply, Matrix.smul_apply, apply_ite] using this
theorem eps_zeta_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ((R.ε : ℤ) : ℂ) * star R.ζ * R.ζ⁻¹ = -1 := by
  rcases R.hζ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
theorem piInf_trace_k (w : InfinitePlace F) {ι : Type} [Fintype ι] (M : Matrix ι ι (AE F E)) : piInf (d.B.emb w) M.trace = (d.cw w M).trace := by
  simp [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, map_sum]
theorem dbl_incM_k : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]
theorem piInf_hT_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) (s t : ℝ) (w : InfinitePlace F) :
    piInf (d.B.emb w) ((((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) =
      ((s * t : ℝ) : ℂ) * ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.piInf_trace_k]
  have hcw : d.cw w (((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ) =
      (((s : ℂ) • d.cw w W) * ((d.b.1.toCols₂).map (d.B.emb w).1)ᵀ)ᵀ * d.A.J.map (d.B.emb w).1 *
        ((((t : ℂ) * (-(((R.sg w : ℤ) : ℂ) * R.ζ))) • d.cw w W) * ((d.b.1.toCols₁).map (d.B.emb w).1)ᵀ).map star *
        ((dbl d.Y.J).map (d.B.emb w).1)ᵀ := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_mul, Matrix.transpose_map]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.dbl_incM_k]
    have c1 := _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.cw_realAd_k (d := d) w s W
    have c2 := _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.cw_realAd_k (d := d) w t (_root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W)
    have c3 := (_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.tw_spec_k R W).2 w
    have c4 := _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d w d.A.J
    have c5 := _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d w d.b.1.toCols₁
    have c6 := _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d w d.b.1.toCols₂
    have c7 := _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d w (dbl d.Y.J)
    have c8 := _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d w ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_mul, Matrix.transpose_map] at c1 c2 c3 c4 c5 c6 c7 c8
    rw [c8, c1, c2, c3, c4, c5, c6, c7, smul_smul]
  rw [hcw, trace_line, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.frame_hermForm_real_sign, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, ← _root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, R.cw_gram w W, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  have hz := _root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R
  have e := _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.eps_zeta_k R
  have sq := _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.sg_sq_k R w
  push_cast
  simp only [star_mul', star_neg, Complex.star_def, Complex.conj_ofReal, map_intCast]
  rw [Complex.star_def] at e
  linear_combination (-(s : ℂ) * t * (((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace) *
    ((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * e + ((s : ℂ) * t * ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace) * sq
end Psi
open Psi
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem psi_tw'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (t : ℝ) (X : Mx F E d.m d.n) :
    d.B.ψ (d.tt (d.gram (realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) X)) =
      Complex.exp (4 * Real.pi * Complex.I * t * ⟪_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X⟫_ℝ) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.psi_tt_arch_k _ (_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.fin_gram_tw_k R W t X), _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.inner_arc_k]
  congr 1
  have e : ∀ w, ((d.cw w (d.gram (realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) X)).trace).re =
      -t * ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := fun w => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.cw_gram_tw_k, Matrix.trace_smul, smul_eq_mul, ← _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.re_trace_loc_k]
    simp [Complex.mul_re]
  simp only [e]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [← Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring_nf
theorem psi_sp'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (s t : ℝ) :
    d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * s * t * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2)) := by
  have hx : finOne F • ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ) = 0 := by
    rw [← Matrix.smul_mul, smul_comm, hW, smul_zero, Matrix.zero_mul]
  have hz : finOne F • (-(((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) = 0 := by
    rw [smul_neg, ← Matrix.trace_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul,
      ← Matrix.transpose_smul, hx]
    simp
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.spf_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.psi_neg_half_trace_k _ hz]
  congr 1
  have e : ∀ w, (piInf (d.B.emb w) (-(((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace)).re =
      -(s * t) * ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w W i j).re + (R.loc w W i j).im * (R.loc w W i j).im) := by
    intro w
    rw [map_neg, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.piInf_hT_k, ← _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.re_trace_loc_k, Complex.neg_re, Complex.re_ofReal_mul]
    ring
  simp only [e]
  rw [← Finset.mul_sum, ← _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.inner_arc_k, real_inner_self_eq_norm_sq]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KFP
end
end
