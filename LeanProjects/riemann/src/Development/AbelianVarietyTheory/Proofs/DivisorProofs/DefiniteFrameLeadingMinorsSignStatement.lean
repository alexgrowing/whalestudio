import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFrameLeadingMinorsSign
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.re_dmin_sign_pos_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 0 ∨ X.p0 = r) → ∀ (x : Frame X.Ψ r) (τ : X.Ψ), (mat x τ).det ≠ 0 → ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  first | exact @GlobalTheory.FlagDomain.definite_frame_leading_minors_sign | exact GlobalTheory.FlagDomain.definite_frame_leading_minors_sign | (intros; apply GlobalTheory.FlagDomain.definite_frame_leading_minors_sign <;> assumption)
