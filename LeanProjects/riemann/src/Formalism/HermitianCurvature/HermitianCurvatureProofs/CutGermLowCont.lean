import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuityAllLevels

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem low_level_continuity : GLCont := by
  intro _ Wp Wq _ _ _ _ _ _ P p nn F Y N Cb _ hF _ j m hm hjm w hw _ a ha
  have hsz : D.ptSize a + m = j + m := by rw [ha.2]
  have hRR := rank_below_compact Wp Wq P p F hF (j + m) hjm w hw.1 a a m hm hsz hsz
  have hn := nPt_app_cont (P := P) (TBB.TTp p) a m
  have e1 : ContinuousOn (fun cc : ℂ × ℂ => TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.1)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := hn.comp continuousOn_fst (fun cc hcc => hcc.1)
  have e2 : ContinuousOn (fun cc : ℂ × ℂ => TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := hn.comp continuousOn_snd (fun cc hcc => hcc.2)
  have hw' : ContinuousOn (fun cc : ℂ × ℂ => ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.1)])) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.2)])) / TBB.normC nn w : ℝ) : ℂ))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_sqrt.comp_continuousOn e1).mul (Real.continuous_sqrt.comp_continuousOn e2)).div_const _)
  exact hw'.mul hRR

end

end Formalism.FourierDecayAlt.P.CutBP
