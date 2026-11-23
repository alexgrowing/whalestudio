import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilChartOfIsChartJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nilChart_reads_of_isChartJ : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw R d) (x : ∀ m : ℕ, Geo.Tor.algOver R (Geo.Tor.JetR R (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ X : Fam G d, NilChart G F.F X ∧ ∀ (OE : Type) [CommRing OE] (io : Out.RingAct G OE) (act : Geo.Tor.Germ.OAct OE F), ChartActs G x io act → ∀ a, Reads X X (io.act a) (act.act a) := by
  first | exact @GlobalTheory.ChF.nilChart_of_isChartJ | exact GlobalTheory.ChF.nilChart_of_isChartJ | (intros; apply GlobalTheory.ChF.nilChart_of_isChartJ <;> assumption)
