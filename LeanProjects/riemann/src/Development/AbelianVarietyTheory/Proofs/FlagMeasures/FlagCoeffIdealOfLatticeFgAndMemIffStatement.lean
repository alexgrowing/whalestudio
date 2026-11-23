import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoeffIdealOfLatticeFgAndMemIff
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (F : Formalism.MainNotions.S.FlagG S r T) (Λ : Submodule (𝓞 E) S.V) (a : Fin r), Λ.FG → (GlobalTheory.RowLatXS.Ia Λ F a).FG ∧ ∀ t : E, t ∈ GlobalTheory.RowLatXS.Ia Λ F a ↔ ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
  first | exact @GlobalTheory.RowLatXS.Ia_fg_and_mem_iff | exact GlobalTheory.RowLatXS.Ia_fg_and_mem_iff | (intros; apply GlobalTheory.RowLatXS.Ia_fg_and_mem_iff <;> assumption)
