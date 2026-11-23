import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingPiecesSmooth
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominating_pieces_smooth : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), IsCptGen ξ → IsCptGen ξ' → Dominates ξ' ξ f i → (∀ p' : X', ∃ (U : X.Opens) (W : X'.Opens) (R : Subring Ω) (C : Subring Ω') (h : ∀ a ∈ R, i a ∈ C), IsPiece ξ U R ∧ IsPiece ξ' W C ∧ W ≤ f ⁻¹ᵁ U ∧ p' ∈ W ∧ ((i.comp R.subtype).codRestrict C (fun a => h a a.2)).Smooth) → Smooth f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces <;> assumption)
