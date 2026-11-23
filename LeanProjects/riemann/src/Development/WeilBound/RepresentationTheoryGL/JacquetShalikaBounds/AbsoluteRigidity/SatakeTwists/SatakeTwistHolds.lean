import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist

namespace PositivityTheory.RgJS

open GlobalTheory.CuspRep

theorem satake_twist_holds : SatTw := by
  intro E _ _ _ m π χ w B hχ h
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

end PositivityTheory.RgJS
