import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Spf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNB

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace Psi

variable {d : SD σ}

theorem psi_tt_arch (M : Mx F E d.n d.n) (hM : finOne F • M = 0) :
    d.B.ψ (d.tt M) = Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ w, 2 * ((d.cw w M).trace).re : ℝ) : ℂ)) := by
  have hf : finOne F • M.trace = 0 := by rw [← Matrix.trace_smul, hM, Matrix.trace_zero]
  have hf' : finOne F * d.tt M = 0 := by
    unfold SD.tt
    rw [← smul_eq_mul, ← LinearMap.map_smul, hf, map_zero]
  rw [d.std.2.2 _ (Place.at_of_finOne hf'), Dense.trace_evI d.cm.1]
  congr 3
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold SD.tt
  rw [Dense.ext_trace d.cm (d.B.emb w), Dense.piInf_cA d.cm]
  have : piInf (d.B.emb w) M.trace = (d.cw w M).trace := by simp [Matrix.trace, SD.cw, map_sum]
  rw [this, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

theorem cw_realAd (w : InfinitePlace F) {p q : Type} (t : ℝ) (Y : Matrix p q (AE F E)) :
    d.cw w (realAd F t • Y) = (t : ℂ) • d.cw w Y := by
  ext i j
  simp [SD.cw, GlobalTheory.RealScalar.piInf_realAd_smul]

theorem tw_spec (R : RD d) (W : Mx F E d.m d.n) :
    finOne F • tw R W = 0 ∧ ∀ w, d.cw w (tw R W) = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W :=
  (exists_tw R W).choose_spec

theorem sg_sq (R : RD d) (w : InfinitePlace F) : ((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]

theorem cw_gram_tw (R : RD d) (W : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) (w : InfinitePlace F) :
    d.cw w (d.gram (realAd F t • tw R W) X) =
      (-(t : ℂ)) • ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w X)) := by
  rw [KW.cw_gram, cw_realAd, (tw_spec R W).2, KW.cw_loc R w W, KW.cw_loc R w X]
  have h3 : ((R.fr w).1 * (Matrix.of (R.loc w X)).map star).map star = (R.fr w).1.map star * Matrix.of (R.loc w X) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h3]
  have hz := KW.zeta_ne R
  have e := KW.frJ R w
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
        linear_combination (-(t : ℂ)) * sg_sq R w

theorem re_trace_loc (R : RD d) (w : InfinitePlace F) (W X : Mx F E d.m d.n) :
    (((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w X)).trace).re =
      ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re]

theorem inner_arc (R : RD d) (W X : Mx F E d.m d.n) :
    ⟪arc R W, arc R X⟫_ℝ =
      ∑ w, ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := by
  simp only [arc, PiLp.inner_apply, EuclideanSpace.equiv, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp
  ring

theorem fin_gram_tw (R : RD d) (W : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) :
    finOne F • d.gram (realAd F t • tw R W) X = 0 := by
  unfold SD.gram
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, smul_comm, (tw_spec R W).1]
  simp

theorem hTens_trace {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, ∑ i, x i j * JA i k * c (y k l) * JB j l := by
        refine Finset.sum_congr rfl fun j _ => ?_
        calc _ = ∑ k, ∑ i, ∑ l, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
          _ = ∑ k, ∑ l, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
              Finset.sum_congr rfl fun k _ => Finset.sum_comm
          _ = ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
              Finset.sum_congr rfl fun i _ => by ring

theorem spf_eq (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    spf d x y = Algebra.trace (AF F) (AE F E)
      (-(xᵀ * incM F d.A.J * y.map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) := by
  unfold spf symp
  rw [hTens_trace, neg_one_mul]

theorem trace_evI_trace (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w, 2 * (piInf (d.B.emb w) z).re := by
  rw [Dense.trace_evI d.cm.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Dense.ext_trace d.cm (d.B.emb w), Dense.piInf_cA d.cm, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

theorem evI_half : evI F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (⅟2) := by
  have ha : evI F (⅟(2 : AF F)) * 2 = 1 := by
    have e1 : evI F (1 : AF F) = 1 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 1 = 1
      exact map_one _
    have e2 : evI F (2 : AF F) = 2 := by
      rw [show (2 : AF F) = 1 + 1 by norm_num, Dense.evI_add, e1]; norm_num
    rw [← e2, ← Dense.evI_mul, invOf_mul_self, e1]
  have hb : algebraMap ℝ (mixedEmbedding.mixedSpace F) (⅟2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul, invOf_mul_self, map_one]
  calc evI F (⅟(2 : AF F)) = evI F (⅟(2 : AF F)) * (algebraMap ℝ (mixedEmbedding.mixedSpace F) (⅟2) * 2) := by
        rw [hb, mul_one]
    _ = (evI F (⅟(2 : AF F)) * 2) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (⅟2) := by ring
    _ = _ := by rw [ha, one_mul]

theorem psi_neg_half_trace (z : AE F E) (hz : finOne F • z = 0) :
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
  rw [e, map_neg, ← Algebra.smul_def, LinearMap.map_smul, trace_evI_trace, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [invOf_eq_inv]
  ring

theorem trace_line {p q r : Type} [Fintype p] [Fintype q] [Fintype r] [DecidableEq q]
    (A : Matrix p q ℂ) (B1 B2 : Matrix r q ℂ) (Jw : Matrix p p ℂ) (Dw : Matrix r r ℂ) (a c : ℂ) :
    ((a • A * B2ᵀ)ᵀ * Jw * (c • A * B1ᵀ).map star * Dwᵀ).trace =
      a * star c * (Aᵀ * Jw * A.map star * (B2ᵀ * Dw * B1.map star)ᵀ).trace := by
  have e1 : (c • A * B1ᵀ).map star = star c • (A.map star * (B1.map star)ᵀ) := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, smul_smul]
  congr 1
  · ring
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]

theorem frame_archimedean_pairing (R : RD d) (w : InfinitePlace F) :
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

theorem eps_zeta (R : RD d) : ((R.ε : ℤ) : ℂ) * star R.ζ * R.ζ⁻¹ = -1 := by
  rcases R.hζ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem piInf_trace (w : InfinitePlace F) {ι : Type} [Fintype ι] (M : Matrix ι ι (AE F E)) : piInf (d.B.emb w) M.trace = (d.cw w M).trace := by
  simp [Matrix.trace, SD.cw, map_sum]

theorem dbl_incM : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]

theorem piInf_hT (R : RD d) (W : Mx F E d.m d.n) (s t : ℝ) (w : InfinitePlace F) :
    piInf (d.B.emb w) ((((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • tw R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) =
      ((s * t : ℝ) : ℂ) * ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace := by
  rw [piInf_trace]
  have hcw : d.cw w (((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • tw R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ) =
      (((s : ℂ) • d.cw w W) * ((d.b.1.toCols₂).map (d.B.emb w).1)ᵀ)ᵀ * d.A.J.map (d.B.emb w).1 *
        ((((t : ℂ) * (-(((R.sg w : ℤ) : ℂ) * R.ζ))) • d.cw w W) * ((d.b.1.toCols₁).map (d.B.emb w).1)ᵀ).map star *
        ((dbl d.Y.J).map (d.B.emb w).1)ᵀ := by
    simp only [SD.cw, Matrix.map_mul, Matrix.transpose_map]
    rw [dbl_incM]
    have c1 := cw_realAd (d := d) w s W
    have c2 := cw_realAd (d := d) w t (tw R W)
    have c3 := (tw_spec R W).2 w
    have c4 := Krd.cw_incM d w d.A.J
    have c5 := Krd.cw_incM d w d.b.1.toCols₁
    have c6 := Krd.cw_incM d w d.b.1.toCols₂
    have c7 := Krd.cw_incM d w (dbl d.Y.J)
    have c8 := Place.cw_cA d w ((realAd F t • tw R W) * (incM F d.b.1.toCols₁)ᵀ)
    simp only [SD.cw, Matrix.map_mul, Matrix.transpose_map] at c1 c2 c3 c4 c5 c6 c7 c8
    rw [c8, c1, c2, c3, c4, c5, c6, c7, smul_smul]
  rw [hcw, trace_line, frame_archimedean_pairing, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, ← KW.cw_gram, R.cw_gram w W, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  have hz := KW.zeta_ne R
  have e := eps_zeta R
  have sq := sg_sq R w
  push_cast
  simp only [star_mul', star_neg, Complex.star_def, Complex.conj_ofReal, map_intCast]
  rw [Complex.star_def] at e
  linear_combination (-(s : ℂ) * t * (((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace) *
    ((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * e + ((s : ℂ) * t * ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace) * sq

end Psi

open Psi

variable {d : SD σ}

theorem psi_tw' (R : RD d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (t : ℝ) (X : Mx F E d.m d.n) :
    d.B.ψ (d.tt (d.gram (realAd F t • tw R W) X)) =
      Complex.exp (4 * Real.pi * Complex.I * t * ⟪arc R W, arc R X⟫_ℝ) := by
  rw [psi_tt_arch _ (fin_gram_tw R W t X), inner_arc]
  congr 1
  have e : ∀ w, ((d.cw w (d.gram (realAd F t • tw R W) X)).trace).re =
      -t * ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := fun w => by
    rw [cw_gram_tw, Matrix.trace_smul, smul_eq_mul, ← re_trace_loc]
    simp [Complex.mul_re]
  simp only [e]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [← Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring_nf

theorem psi_sp' (R : RD d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (s t : ℝ) :
    d.B.ψ (-(⅟(2 : AF F) * spf d ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)
      ((realAd F t • tw R W) * (incM F d.b.1.toCols₁)ᵀ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * s * t * ‖arc R W‖ ^ 2)) := by
  have hx : finOne F • ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ) = 0 := by
    rw [← Matrix.smul_mul, smul_comm, hW, smul_zero, Matrix.zero_mul]
  have hz : finOne F • (-(((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • tw R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) = 0 := by
    rw [smul_neg, ← Matrix.trace_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul,
      ← Matrix.transpose_smul, hx]
    simp
  rw [spf_eq, psi_neg_half_trace _ hz]
  congr 1
  have e : ∀ w, (piInf (d.B.emb w) (-(((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • tw R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace)).re =
      -(s * t) * ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w W i j).re + (R.loc w W i j).im * (R.loc w W i j).im) := by
    intro w
    rw [map_neg, piInf_hT, ← re_trace_loc, Complex.neg_re, Complex.re_ofReal_mul]
    ring
  simp only [e]
  rw [← Finset.mul_sum, ← inner_arc, real_inner_self_eq_norm_sq]
  push_cast
  ring

end PositivityTheory.SiegelWeilFormula.KFP

end
