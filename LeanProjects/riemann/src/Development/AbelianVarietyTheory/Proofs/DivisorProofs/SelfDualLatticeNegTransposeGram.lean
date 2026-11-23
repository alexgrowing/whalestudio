import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Member.selfDualLat_neg_gram_transpose : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D), GlobalTheory.UCls.SelfDualLat (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) := by
  intro D V
  obtain ⟨-, -, hfg, hsp, -, hcc, -, hG, hdet, -, hL⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hint : ∀ z : D.host.E, IsIntegral ℤ z ↔
      z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z
    rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)]
  refine ⟨?_, ?_, hfg, hsp, ?_⟩
  · intro a b
    simp only [Matrix.neg_apply, map_neg, ← hcc, hG]
  · rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  · intro x
    rw [← hL x]
    refine forall_congr' fun y => imp_congr_right fun _ => ?_
    have he : herm (-(V.gram)ᵀ) x y = -(∑ a, ∑ b, x a * V.gramᵀ a b * cF D (y b)) := by
      simp only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, hcc]
    rw [he, hint, ← hint, ← hint]
    exact ⟨fun h => by simpa using h.neg, fun h => h.neg⟩
