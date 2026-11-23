import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algDefStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.QBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthRule

theorem depth_le_scaled_value : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), w.LastPos → ∀ (s : 𝓞 (recB h.toLawsCore).KO), s ≠ 0 → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), ∀ f ∈ T.th j w, (recPJ h j hj).depth s w la y ≤ (((vLa la ((s : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) + vAtV y f := by
  intro D T h j hj w hw s hs la y f hf
  have hc : f ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA w) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj _ hw) f hf
  have hsK : ((s : 𝓞 T.Q.c.F) : T.Q.c.F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hs
  let F : (recB h.toLawsCore).Cusp j w := ⟨f, hc⟩
  have hF : F ∈ (recPJ h j hj).thAll w := Submodule.subset_span hf
  have hsF : s • F ∈ (recPJ h j hj).WWc s w := ⟨F, hF, rfl⟩
  refine (iInf₂_le (s • F) hsF).trans (le_of_eq ?_)
  rw [recPJ_vAt_inc h j hj la y w (s • F)]
  have h1 : (s • F).1 = ((s : 𝓞 T.Q.c.F) : T.Q.c.F) • f := rfl
  rw [h1]
  exact vAtV_smul y _ f hsK

end GlobalTheory.DepthRule
