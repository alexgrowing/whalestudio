import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.FourierStep
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.ContinuousMkG

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KSing

theorem lamSing_of (hCE : CoefEx) (hFZ : FourierZero) (hDW : DenseW) (hAux : AuxiliaryPrimeFunction) : LamSing := by
  intro F E _ _ _ _ _ σ d R w f hf hinv hlam ψ₀ hψ nb hnb g a b
  have htg : IsTopologicalGroup d.G := (hAux F E σ d).2.2.1
  have h0 := fourierStep hCE hFZ hAux d R w f hf hinv hlam ψ₀ hψ nb hnb
  obtain ⟨y, x, rfl, hx⟩ := split d R w g
  have h2 := twoSidedW hDW d R w htg f hf hinv ψ₀ hψ.1 hψ.2.1 nb hnb h0 x (y * a) b
  refine Eq.trans ?_ h2
  congr 1
  funext t
  congr 2
  rw [mul_assoc, hx, ← mul_assoc, ← map_mul]
  simp only [mul_assoc]

end PositivityTheory.SiegelWeilFormula.KSing

end
