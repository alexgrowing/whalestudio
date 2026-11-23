import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLieModelCompleteDvr
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_lie_model_complete_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → (∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left) → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf tX.act.act ρC → ∀ (σ : 𝓞 E →+* T.V) (r : ℕ) (ub : Fin r → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i a, (ub i ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → (∀ a, (w ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) → ∃ cf : Fin r → T.V, IsComb ub cf w) → ∀ yb : Fin r → EC, (∀ i, (MC.pt (yb i)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ) → ∀ L : Submodule T.V EC, (∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ tX.G, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G zV v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) → L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V = Submodule.span T.V (Set.range yb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span <;> assumption)
