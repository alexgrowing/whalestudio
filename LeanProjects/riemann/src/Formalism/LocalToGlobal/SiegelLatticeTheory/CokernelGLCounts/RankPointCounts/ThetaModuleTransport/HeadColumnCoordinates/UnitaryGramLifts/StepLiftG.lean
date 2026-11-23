import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjZzPlusConjEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.LiftPQInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.StepLiftG

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

theorem stepLiftG : StepLiftG := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ γ
  obtain ⟨P, Q, hP, hPQ, hPl, hQl⟩ := liftPQ Z₁ Z₂ γ
  obtain ⟨P₂, Q₂, hP₂, hPQ₂, hP₂l, hQ₂l⟩ := liftPQ Z₂ Z₁ (isoMbeSymm γ)
  obtain ⟨K, -, hKl, hK⟩ := liftPQ_inv Z₁ Z₂ γ P P₂ hP (fun v => hP₂ v) hPl hP₂l
  obtain ⟨K', -, hK'l, hK'⟩ := liftPQ_inv Z₂ Z₁ (isoMbeSymm γ) P₂ P hP₂ (fun v => hP v) hP₂l hPl
  obtain ⟨γ', hγ', hm⟩ := lift_partner (sigR hs) Z₁.Z Z₂.Z Zσ₁.Z Zσ₂.Z _ (lift_zsig hs h₁)
    (lift_zsig hs h₂) (lift_cancel Z₁) (lift_cancel Z₂) P Q P₂ Q₂ K K' hPQ hPQ₂ hK hK'
    hPl hP₂l hQl hQ₂l hKl hK'l
  refine ⟨P, Q, lstar (sigR hs) Q₂, γ', hP, hγ', hPQ, hPl, hQl, fun w => ?_⟩
  obtain ⟨m, hm0, hmw⟩ := hm w
  refine ⟨m, hm0, fun i => ?_⟩
  have hi := congrArg (fun x => ((x i : M.R) : E)) hmw
  simp only [Matrix.mulVec, dotProduct, lstar, Matrix.transpose_apply, Matrix.map_apply,
    Pi.add_apply] at hi ⊢
  push_cast at hi ⊢
  exact hi

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
