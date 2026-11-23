import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicDegenerationArcOfUniformisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_degenerationArc_of_uniformisation : ReciprocityTheory.ChartRestriction.G.Out.Laws → ReciprocityTheory.ChartRestriction.G.Out.Laws2 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition := by
  first | exact @GlobalTheory.HolomorphicArc.main | exact GlobalTheory.HolomorphicArc.main | (intros; apply GlobalTheory.HolomorphicArc.main <;> assumption)
