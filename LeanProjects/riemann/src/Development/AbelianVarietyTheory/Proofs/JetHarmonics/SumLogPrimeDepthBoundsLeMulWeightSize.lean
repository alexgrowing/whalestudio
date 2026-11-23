import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.PtTie

theorem depth_sum_le_PN : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → (WeightAlgebra.DF w : ℝ) * (Real.log (WeightAlgebra.DF w) + 2.2) + (c2 D w * Real.log D.host.QS + cHalf w * Real.log D.host.q + cHalf w * Real.log D.host.d) + ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤ WeightAlgebra.PN D large₂ * w.size := by
  intro D large₂ j w _ hlog
  obtain ⟨-, -, hM, hG, hc, -⟩ := GlobalTheory.RunIn.pPow_size D j w
  have hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.log (WeightAlgebra.DF w : ℝ) := Real.log_natCast_nonneg _
  have hs : (WeightAlgebra.DF w : ℝ) + 1 ≤ w.size := by
    have e : ((WeightAlgebra.DF w : ℕ) : ℝ) = ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ)) := by
      simp [WeightAlgebra.DF, WeightAlgebra.degP, Nat.cast_sum]
    have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
    unfold WeightFamilies.Wt.size
    linarith
  have hg2 : ∀ i, (2 : ℝ) ≤ D.host.g i := fun i => by exact_mod_cast (D.host.g_prime i).two_le
  have hterm : ∀ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤
      (WeightAlgebra.DF w : ℝ) * Real.log (D.host.g i) := fun i =>
    mul_le_mul_of_nonneg_right (div_le_self hD (by linarith [hg2 i])) (Real.log_natCast_nonneg _)
  have hsum : ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤
      (WeightAlgebra.DF w : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rw [Fin.sum_univ_two, Real.log_mul (by linarith [hg2 0]) (by linarith [hg2 1])]
    linarith [hterm 0, hterm 1]
  have hP : 0 ≤ WeightAlgebra.PN D large₂ := by
    unfold WeightAlgebra.PN WeightAlgebra.lamStar
    linarith
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hs hP)
  have h1 := mul_le_mul_of_nonneg_left hlog hD
  unfold WeightAlgebra.PN WeightAlgebra.lamStar
  nlinarith

end GlobalTheory.PtTie
