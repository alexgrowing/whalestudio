import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FewEquationsStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FewEquationsStatement : FewEqSt := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.fewEq | exact GlobalTheory.CompanionTheory.FewEq.fewEq | (intros; apply GlobalTheory.CompanionTheory.FewEq.fewEq <;> assumption)
