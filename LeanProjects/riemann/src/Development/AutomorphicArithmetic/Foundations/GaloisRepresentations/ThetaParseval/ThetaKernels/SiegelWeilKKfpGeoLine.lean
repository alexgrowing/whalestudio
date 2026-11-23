import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoLine
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKKfpGeoRot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpGeo

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem cw_line'_k (w : InfinitePlace F) (P Q : Mx F E d.m d.n) :
    d.cw w (P * (incM F d.b.1.toCols₂)ᵀ + Q * (incM F d.b.1.toCols₁)ᵀ) =
      Matrix.fromCols (d.cw w Q) (d.cw w P) * (d.cw w (incM F d.b.1))ᵀ := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.cw_add'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_transpose'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_transpose'_k]
  conv_rhs => rw [← Matrix.fromCols_toCols (d.cw w (incM F d.b.1))]
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, add_comm]
  rfl
theorem cw_realAd_smul'_k (w : InfinitePlace F) {p q : Type} (r : ℝ) (X : Matrix p q (AE F E)) :
    d.cw w (realAd F r • X) = (r : ℂ) • d.cw w X :=
  GlobalTheory.RealScalar.realAd_smul_map σ d.B.emb d.cm X r w
theorem finOne_smul_line'_k {W W' : Mx F E d.m d.n} (hW : finOne F • W = 0) (hW' : finOne F • W' = 0) (x y : ℝ) :
    finOne F • ((realAd F x • W) * (incM F d.b.1.toCols₂)ᵀ + (realAd F y • W') * (incM F d.b.1.toCols₁)ᵀ) = 0 := by
  rw [smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, smul_comm (finOne F) (realAd F x), hW,
    smul_comm (finOne F) (realAd F y), hW']
  simp
theorem actB_rot_vline'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (z : ℂ) :
    actB (cA σ) (_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t) (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) = _root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W (Complex.exp (-(t * Complex.I)) * z) := by
  have htw := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_tw_k R W).choose_spec
  have hζ : R.ζ ≠ 0 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k
  rw [exp_mul_re', exp_mul_im']
  have hact : ∀ v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E), actB (cA σ) (_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t) v = v * (mat2 (_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t))ᵀ :=
    fun v => rfl
  rw [hact]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k (d := d) (fun w => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_transpose'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.matrixRep_eq_frameConj, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_line'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_line'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_realAd_smul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_realAd_smul'_k,
      _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_realAd_smul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_realAd_smul'_k, show d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) = _ from htw.2 w]
    have hinv : d.cw w (incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) *
        d.cw w (incM F d.b.1) = 1 := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_inv_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_one'_k]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ (d.cw w (incM F d.b.1))ᵀ, ← Matrix.transpose_mul, hinv, Matrix.transpose_one, Matrix.mul_one,
      rot_cols' d.n d.m hζ (R.sg w) t z.re z.im (d.cw w W) _ (_root_.PositivityTheory.SiegelWeilFormula.KFP.dZ_cw_rot'_k R t w)]
  · rw [← Matrix.smul_mul, _root_.PositivityTheory.SiegelWeilFormula.KFP.finOne_smul_line'_k (W' := _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) hW htw.1, _root_.PositivityTheory.SiegelWeilFormula.KFP.finOne_smul_line'_k (W' := _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) hW htw.1,
      Matrix.zero_mul]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
