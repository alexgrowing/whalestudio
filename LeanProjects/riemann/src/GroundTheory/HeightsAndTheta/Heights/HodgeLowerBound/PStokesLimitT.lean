import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTTop
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTVb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem StokesLimitT.proof (hG : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement)
    (hNs : NbarSemipos.Statement) (hTop : StokesLimitTTop.Statement) (hVb : StokesLimitTVb.Statement) :
    StokesLimitT.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hAr hp hpq
  refine ⟨tendsto_nhds_limUnder (hTop II Ψ K ι Ω E D O Lt X B p q hII hAr hp hpq),
    tendsto_nhds_limUnder (hVb II Ψ K ι Ω E D O Lt X B p q hp hpq), ?_⟩
  obtain ⟨t₁, ht₁, hN⟩ := hNs II Ψ K ι Ω E D O Lt X B p q hp hpq

  have ha : ∀ t : ℝ, (X.NbarQ B p q t).a = (X.NbarQ B p q t₁).a := by
    intro t
    simp only [ComponentSetting.NbarQ, smoothRep_a]
    rfl
  have hconst : ∀ᶠ t in 𝓝[>] (0 : ℝ), X.degN B p q t₁ = X.degN B p q t := by
    filter_upwards [Ioc_mem_nhdsGT ht₁] with t ht
    unfold ComponentSetting.degN
    rw [hG K ι Ω D.y D.n _ D.arith (hN t ht.1 ht.2).1, hG K ι Ω D.y D.n _ D.arith (hN t₁ ht₁ le_rfl).1, ha t]
  exact tendsto_nhds_limUnder ⟨_, tendsto_const_nhds.congr' hconst⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
