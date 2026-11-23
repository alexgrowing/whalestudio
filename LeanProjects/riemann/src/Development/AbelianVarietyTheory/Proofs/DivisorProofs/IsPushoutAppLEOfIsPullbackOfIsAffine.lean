import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine

open AlgebraicGeometry CategoryTheory Limits

set_option autoImplicit false

namespace GlobalTheory.AffBaseChange

theorem isPushout_appLE_of_isPullback_of_isAffine :
    ∀ (X X' S S' : Scheme.{0}) (f : X' ⟶ X) (g : X' ⟶ S') (p : X ⟶ S) (q : S' ⟶ S),
      IsPullback f g p q → IsAffine S → IsAffine S' → ∀ (W : X.Opens), IsAffineOpen W →
      IsPushout (p.appLE ⊤ W (fun _ _ => trivial)) q.appTop (f.app W)
        (g.appLE ⊤ (f ⁻¹ᵁ W) (fun _ _ => trivial)) := by
  intro X X' S S' f g p q h hS hS' W hW
  haveI : IsAffineHom q := inferInstance
  have P := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE h.flip this (isAffineOpen_top S) hW
    (fun _ _ => trivial) (fun _ _ => trivial)
  exact P.flip

end GlobalTheory.AffBaseChange
