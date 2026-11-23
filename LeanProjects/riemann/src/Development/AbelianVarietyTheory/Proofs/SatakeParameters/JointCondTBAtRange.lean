import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JumpWindow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpWindowOfJumpSetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowBlockExponentConditionOfJumpWindowStatement

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

theorem jointTB_iff_jointCond (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ) :
    JointTB D HW F i r π M0 h0 cB ↔ JointConditionTameBound D HW F i r π M0 h0 cB := by
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun w hw => ?_⟩
    obtain ⟨a, b, c⟩ := h w hw
    exact ⟨a, b, fun C hs Y hc hY => c C.LL C.le hs Y hc hY⟩
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun w hw => ?_⟩
    obtain ⟨a, b, c⟩ := h w hw
    exact ⟨a, b, fun CL hL hs Y hc hY => c ⟨CL, hL⟩ hs Y hc hY⟩

theorem jointCond_TB_at_range (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D)
    (hJ : AdmissibleParameterJ.JumpConditions large₂) (hA : EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (cB : ℕ)
    (h2 : D.nd.l i ∉ D.host.small) (hq : D.nd.l i ≠ D.host.q) (hd : D.nd.l i ≠ D.host.d) (hG : GoodR D.nd i r)
    (hc : GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ cB) :
    ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i r π M0 h0 cB := by
  obtain ⟨ht, hW⟩ := GlobalTheory.T.hodgeTateJumpWindow_of_jumpSets D large₂ hJ hA
  have hT := GlobalTheory.T.jumpWindowBlockExponentCondition_of_jumpWindow D HW F i r π ⌊2 * large₂.sc.b⌋₊ h2 hq hd ht (hW i r hG π)
  exact ⟨_, _, (jointTB_iff_jointCond D HW F i r π _ _ _).1 (hT.mono hc)⟩

end GlobalTheory.BlockWindow

end
