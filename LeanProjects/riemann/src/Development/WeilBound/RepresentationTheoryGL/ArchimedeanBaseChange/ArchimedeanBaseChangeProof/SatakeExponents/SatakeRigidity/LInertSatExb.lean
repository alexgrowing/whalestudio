import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.StFull
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.F.Rig.B

theorem inertSatEx : InertSatEx := by
  intro E _ _ _ hE n π hπ w hw hu
  exact GlobalTheory.BcSpehCompare.exists_hasSatAt (fun v => hE v) hπ hw hu

end PositivityTheory.Rg.BcB.F.Rig.B

end
