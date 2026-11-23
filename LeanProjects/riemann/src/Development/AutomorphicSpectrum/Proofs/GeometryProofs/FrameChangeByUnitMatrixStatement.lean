import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrix
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_change_by_unit_matrix : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (β : Fin r → E) (q : Cpt ξ) (P : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt β q → (∀ a b, P a b ∈ regAt ξ q) → unitAt ξ q P.det → L.IsFrameAt (fun k => ∑ a, P a k • β a) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb | exact GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb <;> assumption)
