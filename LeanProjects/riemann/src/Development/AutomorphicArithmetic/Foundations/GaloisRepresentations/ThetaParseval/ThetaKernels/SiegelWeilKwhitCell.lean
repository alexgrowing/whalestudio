import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GramZeroLeft
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (_hΦ : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := by
  have h0 : d.dd.rho d.B.ψ 0 Φ = Φ := by
    funext y
    simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Matrix.zero_mul, h0]
theorem gram_zero_left_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Z : Mx F E d.m d.n) : d.gram 0 Z = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem cellFormula_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CellFormula_k := by
  intro hT F E _ _ _ _ _ σ d ν hν ε w hw Φ hΦ g x β hg
  have h1 : d.sec0 Φ (w * g * x) = d.l (d.om w (d.om g (d.om x Φ))) := by
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_mul, Module.End.mul_apply]
  have hx := _root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d x hΦ
  have hgx := _root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d g hx
  rw [h1, ← _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_zero_k d (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d w hgx), hT.2.2.1 F E σ d ν hν ε w hw _ hgx 0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.gram_zero_left_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_mul]
  exact (hT.2.1 F E σ d _ hx).1 g β hg Z
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
