import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionDilationExp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLawC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLawB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem j_comm_dil_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (w : InfinitePlace F) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single L.i₀ 1) τ y) (g : L.sd.G) : L.j g * R.ι w y = R.ι w y * L.j g := by
  apply PositivityTheory.SiegelWeilFormula.kfour.inFrame_injective d.b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil_k R w L.i₀ τ y hy]
  ext u v
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hv : v ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n))
  · rw [((L.j_out g) v hv u).2, Matrix.one_apply]
    split_ifs with huv
    · subst huv; ring
    · simp
  · by_cases hu : u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n))
    · rw [((L.j_out g) u hu v).1, Matrix.one_apply]
      split_ifs with huv
      · subst huv; ring
      · simp
    · rw [dilV_off d.cm w L.i₀ τ u hu, dilV_off d.cm w L.i₀ τ v hv, one_mul, mul_one]
theorem l_eq_T_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) : d.l Ψ = d.T Ψ 0 := by
  have h1 := d.ok.dbl.kill 0 Ψ hΨ
  have h2 : ∀ M : Matrix (Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), (0 : Matrix (Fin d.m) (Fin d.n) (AE F E)) * M = 0 :=
    fun M => Matrix.zero_mul M
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.T
  rw [← h1]
  congr 2
  ext i j
  exact (congrFun (congrFun (Matrix.zero_mul (diagCols (Fin d.n))ᵀ) i) j).trans
    (congrFun (congrFun (Matrix.zero_mul (incM F d.b.1.toCols₂)ᵀ) i) j).symm
theorem inFrame_dil'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (dilT d.cm w i₀ τ).1 0 0 (dilT d.cm w i₀ (-τ)).1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil_k R w i₀ τ y hy]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal_apply, dilT, dilV]
theorem constantTerm_dilation (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (h : d.G) :
    d.sec0 Φ (R.ι w y * h) = Complex.exp (τ * d.m) * d.sec0 Φ h := by
  haveI := d.cm.1
  have hpres : ∀ x, ∀ Ψ ∈ d.sch, d.om x Ψ ∈ d.sch := d.ok.dbl.weil.2.1.pres
  have hΨ := hpres h Φ hΦ
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0
  rw [map_mul, Module.End.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.AStep.l_eq_T_k d _ (hpres _ _ hΨ), _root_.PositivityTheory.SiegelWeilFormula.AStep.l_eq_T_k d _ hΨ,
    ((H.tAll.2.1 F E σ d _ hΨ).2.1 (R.ι w y) (dilT d.cm w i₀ τ) (dilT d.cm w i₀ (-τ)) (_root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil'_k R w i₀ τ y hy) 0),
    det_dilT, _root_.PositivityTheory.SiegelWeilFormula.AStep.chi_adrU_k d w τ, absE_adrU d.cm w τ]
  have hz : ∀ M : Matrix (Fin d.n) (Fin d.n) (AE F E), d.T (d.om h Φ) ((0 : Mx F E d.m d.n) * M) = d.T (d.om h Φ) 0 :=
    fun M => congrArg _ (Matrix.zero_mul M)
  rw [hz, ← Real.exp_mul, Complex.ofReal_exp, one_mul]
  congr 2
  push_cast; ring
end PositivityTheory.SiegelWeilFormula.AStep
end
end
