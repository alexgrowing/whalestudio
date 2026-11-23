import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.WithThModelLet
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.WBound
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestOneOpOf
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.DoubleMonomialApply
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.XXgZeroP
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.GeoTouch
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RenameMemSupported
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.CompDEqHomComp
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ValSCongrSupp
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PmatDetMem
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.FortyEightBoundArith
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ProdRangeZmod
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.SupportedOfSupport
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.SumFiberMultideg
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.MemTSetIff
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.MultidegSingle
import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.Lam1SPderivAndXMulLeAddIndicator
import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.GeZSum

noncomputable section

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem opSteps_of (h : NoOpStep) : OpSteps :=
  ⟨trDerPl, trDerNo, trMulPl, trMulNo, plDer, plEul, plMul, h, geoTop, geoTouch⟩

theorem restWord_of_steps (h : OpSteps) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestWord D CLa Ck Crk Cdeg :=
  restWord_of D CLa Ck Crk Cdeg restLeOfG (restOneOp_of h D CLa Ck Crk Cdeg) (restWordBound D CLa Ck Crk Cdeg)

theorem restMEM_of_last (hNO : NoOpStep) (hPl : RestPl)
    (hAr : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, RestArithStep C CLa)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMEM D CLa Ck Crk Cdeg :=
  memCondition_of_theoremII D CLa Ck Crk Cdeg
    (lemma5a_of_monomial D CLa Ck Crk Cdeg
      (rest5aMono_of_cut restT (restN D) restTh hPl restSP hAr D CLa Ck Crk Cdeg))
    (restWord_of_steps (opSteps_of hNO) D CLa Ck Crk Cdeg)

theorem stmtE_of_last (D : Formalism.BasicNotions.D7) (hNO : NoOpStep) (hPl : RestPl)
    (hAr : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, RestArithStep C CLa) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  Formalism.MainNotions.Proposition5Numerics.stmtE_of_mem D (fun CLa Ck Crk Cdeg => restMEM_of_last hNO hPl hAr D CLa Ck Crk Cdeg)

theorem stmtE_of_pl (D : Formalism.BasicNotions.D7) (hPl : RestPl) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_last D Formalism.MainNotions.LetterSubstitution.noOpStep hPl ⟨1, one_pos, fun C hC CLa => arithCondition_of_one_le C CLa hC⟩

theorem level_link_of_degree_letters (hLL : LinkL) (hDg : LkDeg) (hVr : LkVars) : RestLink :=
  restLink_of Formalism.MainNotions.LetterSubstitution.valNN Formalism.MainNotions.LetterSubstitution.homDec hLL hDg hVr restTr (fun Fr jz μ => lkW Fr jz μ)

private theorem restPl_of_restChain_of_restLink (hC : RestChain) (hL : RestLink) : RestPl := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr L₁ N₁ hV hE J _ Dt hT hJ A hA l hl ga hg t ht dPl
  exact ⟨hC p n' r K m O hk Fr L₁ N₁ hV hE J Dt hT hJ A hA l hl ga hg t ht dPl,
    hL p n' r K m O hk Fr L₁ N₁ hV hE J Dt hT hJ A hA l hl ga hg t ht dPl⟩

theorem restLink : RestLink := level_link_of_degree_letters linkL lkDeg lkVars

theorem stmtE_of_chain (D : Formalism.BasicNotions.D7) (hC : RestChain) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_pl D (restPl_of_restChain_of_restLink hC restLink)

end Formalism.MainNotions.PairMembershipBlocks
