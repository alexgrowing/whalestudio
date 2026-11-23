import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.LamSingOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingTS

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
theorem lamSing_of_k (hCE : _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k) (hFZ : _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k) (hDW : _root_.PositivityTheory.SiegelWeilFormula.DenseW_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k := by
  intro F E _ _ _ _ _ σ d R w f hf hinv hL ψ₀ hψ nr hnr g a b
  have hG : IsTopologicalGroup d.G := (hAux F E σ d).2.2.1
  obtain ⟨y, x, rfl, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.split_k d R w g
  have h0 := _root_.PositivityTheory.SiegelWeilFormula.KSing.fourierStep_k hCE hFZ hAux d R w f hf hinv hL ψ₀ hψ nr hnr
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.KSing.twoSidedW_k hDW d R w hG f hf hinv ψ₀ hψ.1 hψ.2.1 nr hnr h0 x (y * a) b
  have e : ∀ t, R.ι w y * x * R.ι w (a * nr t * b) = R.ι w (y * a * nr t * b) * x := fun t => by
    rw [mul_assoc, hx, ← mul_assoc]
    simp only [map_mul, mul_assoc]
  simp_rw [e]
  exact h2
end PositivityTheory.SiegelWeilFormula.KSing
end
end
