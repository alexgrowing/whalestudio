import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_eq_of_full_intersection_system : GlobalTheory.CompanionTheory.MixZ.PtDict → GlobalTheory.CompanionTheory.MixZ.CodimOne → GlobalTheory.CompanionTheory.MixZ.ExistsRat → GlobalTheory.CompanionTheory.MixZ.CycleOfRat → GlobalTheory.CompanionTheory.MixZ.ArchIntEq → GlobalTheory.CompanionTheory.MixZ.VertEq → GlobalTheory.CompanionTheory.MixZ.PtLen → GlobalTheory.CompanionTheory.MixZ.CurveInt → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement → ∀ II : ReciprocityTheory.ChartRestriction.G.Geo.IntersectionSystem, ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II → GlobalTheory.CompanionTheory.MixZ.HeightEq II := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.heightEq_holds | exact GlobalTheory.CompanionTheory.MixZ.heightEq_holds | (intros; apply GlobalTheory.CompanionTheory.MixZ.heightEq_holds <;> assumption)
