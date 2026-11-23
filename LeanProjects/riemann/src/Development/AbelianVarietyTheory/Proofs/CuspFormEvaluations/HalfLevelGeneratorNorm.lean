import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem half_level_generator_norm :
    ∀ (D : D7) (T : Top D) (_h : LawsP T) (_EX : ErrX D), ∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α} := by
  intro D T h _EX
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM

  have hbb : ∀ x : 𝓞 D.host.E, T.Q.H.bar (T.Q.H.bar x) = x := by
    intro x
    rw [bar_core T.toCore, bar_core T.toCore, barE_barE]

  have hn : ∀ i, piOf T.toCore _EX i * T.Q.H.bar (piOf T.toCore _EX i) = (D.host.g i : 𝓞 D.host.E) := by
    intro i
    rw [bar_core T.toCore]
    exact piOf_mul_barE T.toCore _EX i
  set π₀ := piOf T.toCore _EX 0
  set π₁ := piOf T.toCore _EX 1
  refine ⟨T.Q.H.bar (π₀ * π₁), ?_, ?_⟩
  · rw [hbb, map_mul, level_M T.toCore hM]
    have h0 := hn 0
    have h1 := hn 1
    push_cast
    rw [← h0, ← h1]
    ring
  · rw [hbb, Mb_eq T.toCore hM, ← span_piOf T.toCore hM _EX 0, ← span_piOf T.toCore hM _EX 1,
      Ideal.span_singleton_mul_span_singleton]

end GlobalTheory.RunIn
