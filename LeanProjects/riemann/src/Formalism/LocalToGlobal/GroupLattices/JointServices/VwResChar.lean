import Formalism.LocalToGlobal.GroupLattices.JointServices.ValIntNonneg
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.NumbersP

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV

noncomputable section

namespace Formalism.L2.G.ServJoint

theorem vw_resChar (D : D7) (w : D.what₂.places.Pl) :
    Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
  have hp0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D.what₂.places.resChar_prime w).ne_zero
  have h1 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hp0, vAdd_eq_vw _ _ hp0] at h1
  exact_mod_cast h1

theorem plc_plEq (D : D7) (w : D.what₂.places.Pl) : Formalism.EigenvalueLevelCeiling.plc (D.plEq w) = D.what₂.places.resChar w := by
  by_contra hne
  have h0 := Formalism.L2.DIV.vw_prime_eq_zero (D.plEq w) (D.what₂.places.resChar_prime w) (fun h => hne h.symm)
  rw [vw_resChar] at h0
  have := D.what₂.places.ramIdx_pos w
  omega

end Formalism.L2.G.ServJoint

end
