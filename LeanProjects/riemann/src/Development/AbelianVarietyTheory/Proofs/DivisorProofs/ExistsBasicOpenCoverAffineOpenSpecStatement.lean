import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAffineOpenSpec
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_cover_affineOpen_spec : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (u : Sp S ⟶ Y),
    ∃ (n : ℕ) (s : Fin n → S) (W : Fin n → Y.Opens), Ideal.span (Set.range s) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧ ∀ i, (spMap (algebraMap S (Localization.Away (s i))) ≫ u) ⁻¹ᵁ W i = ⊤ := by
  first | exact @GlobalTheory.SecGlue.exists_basicOpen_cover_affine | exact GlobalTheory.SecGlue.exists_basicOpen_cover_affine | (intros; apply GlobalTheory.SecGlue.exists_basicOpen_cover_affine <;> assumption)
