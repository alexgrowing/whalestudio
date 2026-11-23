import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpens
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_restriction_compatible_opens : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V W : (Y (e + 1)).left.Opens) (V' W' : (Y e).left.Opens) (hV : V' ≤ β e ⁻¹ᵁ V) (hW : W' ≤ β e ⁻¹ᵁ W) (h : W ≤ V) (h' : W' ≤ V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V), redL I Y β hβ L w hL e W W' hW (SecOnR.restrict _ _ h x) = SecOnR.restrict _ _ h' (redL I Y β hβ L w hL e V V' hV x) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict <;> assumption)
