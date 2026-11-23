import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonMapsBijectiveFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_maps_bijective_finite : ∀ (R S P : Type) [CommRing R] [CommRing S] [Algebra R S] [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧ Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.th_bijective | exact GlobalTheory.CompanionTheory.PerfVB.th_bijective | (intros; apply GlobalTheory.CompanionTheory.PerfVB.th_bijective <;> assumption)
