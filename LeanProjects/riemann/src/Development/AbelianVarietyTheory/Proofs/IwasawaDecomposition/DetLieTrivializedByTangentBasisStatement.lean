import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetLieTrivializedByTangentBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmpStOfSabExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFiberNormalReduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_lie_trivialized_by_tangent_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β)
    (hL : (GlobalTheory.FlagMod.detLie Z).IsLB) (W : Scheme.{0}) (p : W ⟶ Z.X) (G : Over W) [GrpObj G] [IsCommMonObj G]
    (ψ : G.left ⟶ Z.t.G.left), IsGrpPullback G Z.t.G p ψ → ∀ (d : ℕ)
    (B : ∀ (S : Type) [CommRing S] (x : Sp S ⟶ W), Module.Basis (Fin d) S (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x G)),
    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ W) (x' : Sp S' ⟶ W)
      (e : spMap φ ≫ x = x') (j : Fin d), tanPull φ e (B S x j) = B S' x' j) →
    GlobalTheory.CechPic.pull p (GlobalTheory.CechPic.cls _ hL) = 0 := by
  first | exact @GlobalTheory.PolFin.pull_cls_detLie_eq_zero_of_frame | exact GlobalTheory.PolFin.pull_cls_detLie_eq_zero_of_frame | (intros; apply GlobalTheory.PolFin.pull_cls_detLie_eq_zero_of_frame <;> assumption)
