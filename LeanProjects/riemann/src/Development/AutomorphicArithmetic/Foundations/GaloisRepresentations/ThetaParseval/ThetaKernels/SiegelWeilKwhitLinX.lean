import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.LinRedC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCutX
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitLin

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem linRedC_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k := by
  intro hT hTC hLB hU hS c F E _ _ _ _ _ σ d hE k cs Φs hK x hW nb lam 𝓖 hcd ε w hw T hND
  have hTT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k := hT.2.2.2.1
  have hTA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k := hT.2.2.2.2
  have hsch : ∀ i ∈ (Finset.univ : Finset (Fin k)), Φs i ∈ d.sch := fun i _ => (hK i).1
  have hsum := _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_sum_mem_k d Finset.univ cs Φs hsch
  have hIfun : d.I (∑ i, cs i • Φs i) = ∑ i, cs i • d.I (Φs i) := by
    funext y; rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_I_sum_k d hTT hTA Finset.univ cs Φs hsch y]; simp [Finset.sum_apply]
  have horb : d.orb T (d.om x (∑ i, cs i • Φs i)) = ∑ i, cs i * d.orb T (d.om x (Φs i)) := by
    rw [← hTC F E σ d _ hsum nb lam 𝓖 hcd T x, hIfun,
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_fc_sum_k hLB d hcd T hND x Finset.univ cs (fun i => d.I (Φs i)) (fun i => ((hTA F E σ d).2.2 _ (hK i).1).2.1)
        (fun i => ((hTA F E σ d).2.2 _ (hK i).1).2.2)]
    exact Finset.sum_congr rfl fun i _ => by rw [hTC F E σ d _ (hK i).1 nb lam 𝓖 hcd T x]
  have horbc : c * d.orb T (d.om x (∑ i, cs i • Φs i)) = ∑ i, cs i * (c * d.orb T (d.om x (Φs i))) := by
    rw [horb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  choose t ht using fun i => hU F E σ d (s0 d.m d.n) (d.sec0 (Φs i)) (hS F E σ d (Φs i) (hK i)) (hE (Φs i) (hK i))
  have hval := lin_holValueAt_sum Finset.univ cs
    (fun i z => ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
    (fun i => c * d.orb T (d.om x (Φs i))) (s0 d.m d.n) (fun i _ => hW i nb lam 𝓖 hcd ε w hw T hND)
  rw [horbc]
  refine hval.congr ⟨∑ i, |t i|, fun z hz => ?_⟩
  have hzi : ∀ i, t i < z.re := fun i => lt_of_le_of_lt
    ((le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i))) hz
  have hint : ∀ i, Integrable (fun β => flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (T.1.1 * β.1))) lam := fun i =>
    ((ht i z (hzi i) nb lam 𝓖 hcd ε w hw x).1).mul_bdd (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_psi_meas_k d T.1.1).aestronglyMeasurable
      (Eventually.of_forall fun β => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
  show ∑ i, cs i * ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
    ∫ β, flat d.a (d.sec0 (∑ i, cs i • Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
  refine (Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm).trans ?_
  rw [← integral_finsetSum _ fun i _ => (hint i).const_mul (cs i)]
  congr 1
  funext β
  simp only [flat, _root_.PositivityTheory.SiegelWeilFormula.KWhit.constantTerm_finsetSum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
