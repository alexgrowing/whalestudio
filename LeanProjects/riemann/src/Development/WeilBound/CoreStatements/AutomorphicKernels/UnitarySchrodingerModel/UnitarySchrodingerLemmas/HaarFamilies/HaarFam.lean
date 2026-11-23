import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.HaarFam
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory

namespace PositivityTheory.PfSWUS.SwMatch

theorem haarFam : HaarFam := by
  intro D n
  have key : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      ∃ m : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E), m.IsAddHaarMeasure := by
    intro v
    have := (GlobalTheory.LocalDensityCompare.lcs (E := D.host.E) v).1
    have := (GlobalTheory.LocalDensityCompare.lcs (E := D.host.E) v).2.1
    have := GlobalTheory.LocalDensityCompare.topRing (E := D.host.E) v
    have : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : BorelSpace (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) := Pi.borelSpace
    exact ⟨Measure.addHaar, inferInstance⟩
  choose lam hlam using key
  exact ⟨lam, hlam⟩

end PositivityTheory.PfSWUS.SwMatch

end
