import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.SplitDomOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilSteps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilTheta

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem splitDom_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.Kdil.DecompW_k) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.SplitDom_k := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ g
  obtain ⟨x, y₀, hg, hx⟩ := hD F E σ d R w g
  obtain ⟨A, hA⟩ := hAw F E σ d R w x hx
  have hind : d.Indep w Ψ := ((_root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k F E σ d R).2.1 w Ψ hΨ).2
  refine ⟨y₀, A Ψ, ?_, ?_⟩
  · intro Φ hΦ f hf hTΦ y
    obtain ⟨hLf, hLΦ⟩ := hL (y₀ * y) f hf
    have h1 := hLΦ Ψ hind Φ hΦ hTΦ
    rw [hg, mul_assoc, ← map_mul, map_mul, Module.End.mul_apply]
    exact ((hA Ψ hind).2 _ hLf _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.om_mem_k d _ hΦ) h1)
  · intro δ hδ
    obtain ⟨Φ, hΦ, hTΦ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftSw1_k hT.1 d R w _ (isSw_gauss hδ) Ψ hΨ
    rw [← (hA Ψ hind).2 _ (isSw_gauss hδ) Φ hΦ hTΦ]
    exact (hT.1 F E σ d).1 _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.om_mem_k d x hΦ)
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
