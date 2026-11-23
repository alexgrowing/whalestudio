import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisPullbackCompatible
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
theorem _root_.GlobalTheory.T.tangent_basis_pullback_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    (tK : SAB H (Sp K)), ∃ (d : ℕ) (B : ∀ (S : Type) [CommRing S] (y : Sp S ⟶ Sp K),
      Module.Basis (Fin d) S (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM y tK.G)),
      ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (y : Sp S ⟶ Sp K) (y' : Sp S' ⟶ Sp K)
        (e : spMap φ ≫ y = y') (j : Fin d), tanPull φ e (B S y j) = B S' y' j := by
  first | exact @GlobalTheory.LieFrameField.lieFrame_baseChange | exact GlobalTheory.LieFrameField.lieFrame_baseChange | (intros; apply GlobalTheory.LieFrameField.lieFrame_baseChange <;> assumption)
