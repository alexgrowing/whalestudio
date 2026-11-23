import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem redL_restrict : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V W : (Y (e + 1)).left.Opens) (V' W' : (Y e).left.Opens) (hV : V' ≤ β e ⁻¹ᵁ V) (hW : W' ≤ β e ⁻¹ᵁ W) (h : W ≤ V) (h' : W' ≤ V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V), redL I Y β hβ L w hL e W W' hW (SecOnR.restrict _ _ h x) = SecOnR.restrict _ _ h' (redL I Y β hβ L w hL e V V' hV x) := by
  intro R _ I Y β hβ L w hL e V W V' W' hV hW h h' x
  have key := SecOnR.pull_restrict (M := L (e + 1)) (toR_w I Y β hβ e) h h' hV hW x
  apply (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 W')).injective
  simp only [redL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [key]
  obtain ⟨y, hy⟩ := (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 V')).surjective (SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V V' hV x)
  rw [← hy, LinearEquiv.symm_apply_apply]
  exact (SecOn.congr_restrict (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 h' y).symm

end GlobalTheory.CompanionTheory.FormalAlg.Lift
