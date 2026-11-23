import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSecOfAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSecOf_action : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) [QuasiSeparated t.G.hom] {T : X.Opens} (h : CoordOpen t T) (v : TanM (affPt h.1) t.G) (l : Γ(GlobalTheory.LieVB.Lie t.G, T)) (a : 𝓞 E), IsSecOf h.1 v l → IsSecOf h.1 (actR t.act a v) ((GlobalTheory.VB.act (GlobalTheory.LieVB.lieAct t.act) a).app T l) := by
  first | exact @GlobalTheory.LocM.IsSecOf.act | exact GlobalTheory.LocM.IsSecOf.act | (intros; apply GlobalTheory.LocM.IsSecOf.act <;> assumption)
