import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedOfLocalAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_of_local_adapted : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {ι : Type} [Fintype ι] {L : X.Modules} {g : ℕ}
    {E E' : ι → X.Modules} {r : ι → ℕ} (hL : VMetric p L g) {m : ℕ} (o : ι ≃ Fin m) (h : ∀ a, VMetric p (E a) (r a))
    (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a), (∀ a, Mono (u a)) →
    (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ LocAdapted r (fun a => (o a : ℕ)) T u V) → OrthEmb hL h T → IsGraded hL o h u := by
  first | exact @GlobalTheory.GrFilt.isGraded_of_locAdapted | exact GlobalTheory.GrFilt.isGraded_of_locAdapted | (intros; apply GlobalTheory.GrFilt.isGraded_of_locAdapted <;> assumption)
