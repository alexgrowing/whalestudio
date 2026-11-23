import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationDataNormalRing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_data_normal_ring : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), IsGrpPullback F.univ.A G j e → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (I : Ideal R) (ξ : Sp R ⟶ S) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : Unif I D A G'), IsUnifOf F j e ξ π U → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R) (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (β : B.left ⟶ G'.left) (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), y ≫ j = x ≫ ξ → IsGrpPullback B G' x β → IsGrpPullback B F.univ.A y α → α ≫ e = β ≫ π → IsSquare α α₂ → LBIso (abelian₂ B (U.LG.L.pull β)) (F.univ.P.pull α₂) := by
  first | exact @GlobalTheory.UnifLamFibre.lam_pull_eq_univ | exact GlobalTheory.UnifLamFibre.lam_pull_eq_univ | (intros; apply GlobalTheory.UnifLamFibre.lam_pull_eq_univ <;> assumption)
