import Development.WeilBound.CoreStatements.SatakeConjugation.CsdDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

namespace PositivityTheory.NCmp

open GlobalTheory.CuspRep GlobalTheory.ThetaPull

theorem thetaTw : ThetaTw := fun L _ _ _ a π =>
  ⟨thetaSub π, (pull L a).submoduleMap π.V, fun o φ => Subtype.ext (act_pull o φ.1).symm⟩

end PositivityTheory.NCmp
