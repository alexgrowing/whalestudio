import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleRelativelyAcyclic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_line_bundle_relatively_acyclic : GlobalTheory.Published.AmpleVanishing → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → IsRelAcyclic (A.hom ≫ p) A.hom L := by
  first | exact @GlobalTheory.RelAcyclicAmple.isRelAcyclic_of_relAmple | exact GlobalTheory.RelAcyclicAmple.isRelAcyclic_of_relAmple | (intros; apply GlobalTheory.RelAcyclicAmple.isRelAcyclic_of_relAmple <;> assumption)
