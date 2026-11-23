import CompanionTheory.AutomorphicTheory.CompactTopologicalForms.NormalFormTopDomination
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.UpdateEqUMinus
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.LimStepsOf
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.SmoothCoefficientBessel

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBPEq
open CompanionTheory.LimBd.Main (ZuckT ZuckDualT zuckT_of_zuck zuckDualT_of_zuckDual)

theorem asymptotic_different_types : AsmDiff := by
  intro Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := CutBP.CompactFormNormalFormDomination.thmBpAt_top Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA _
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA

theorem asymptotic_equal_types : AsmEq := by
  intro Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := CutBPEq.CompactFormNormalFormDomination.thmBpAt_eqR_top Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnp hnm hDp hDm hf
    hfA _ _
  exact h P Wp Wq p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnp hnm hDp hDm hf hfA

end CompanionTheory.WaveGrid
