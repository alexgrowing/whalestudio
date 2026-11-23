import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piece_localization_at_element : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (R : Subring Ω) (a : Ω), IsCptGen ξ → IsPiece ξ U R → a ∈ R → a ≠ 0 → ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece <;> assumption)
