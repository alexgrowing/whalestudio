import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickening
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_eq_of_square_zero_thickening : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens, u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  first | exact @GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | exact GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | (intros; apply GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero <;> assumption)
