import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructure
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_module_structure : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G) (O : Type) [CommRing O] (act : OAct O G), letI := τ.addCommGroup; letI := τ.grpB; (∀ a, ∃ b : τ.B ⟶ τ.B, IsMonHom b ∧ act.act a ≫ τ.q = τ.q ≫ b) → ∃ m : Module O τ.X, letI := m; ∀ a, (GlobalTheory.Diag.diagAct (Sp K) O τ.X).act a ≫ τ.i = τ.i ≫ act.act a := by
  first | exact @GlobalTheory.CompanionTheory.TorusAct.exists_module_diagAct | exact GlobalTheory.CompanionTheory.TorusAct.exists_module_diagAct | (intros; apply GlobalTheory.CompanionTheory.TorusAct.exists_module_diagAct <;> assumption)
