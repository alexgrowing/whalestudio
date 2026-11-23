import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeAndArithmeticCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoZeroOfOpenSetLinearRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDifferenceTelescopingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeLinearRootSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPotentialTruncationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoMixedIntegralDifferenceZeroStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open GlobalTheory.ArDegIndep

namespace GlobalTheory.ArDegIndep

theorem limit_indep : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ B : ℝ, 2 ≤ B → ∀ u : D.what₂.Tau → Fin O.N → ℝ, Filter.Tendsto (fun R : ℝ => O.Y.arDeg (GlobalTheory.FlagAr.setB O.Y B) R (linRoot u ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N + 1)) - (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x' O.Φ)).arDeg (GlobalTheory.FlagAr.setB O.Y B) R (linRoot u ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N + 1))) Filter.atTop (nhds 0) := by
  intro h2 hH D O hC hf A T H h x' B hB v
  have hT := (GlobalTheory.T.degree_and_arithmetic_compatibility h2 hH D O hC hf A T H h).1
  have hI := GlobalTheory.T.fibre_size_and_range_bound h2 hH D O hC hf A T H h
  have hsm : ∀ R : ℝ, 2 ≤ R → ∀ (u : Wt O.Y) (c : O.Y.Comp), (T.M c).Smooth ((T.F c).phR R u) := by
    intro R hR u c σ
    obtain ⟨b, p, -, C, hC'⟩ := (hI c).2 σ
    exact (hC' u R hR).1
  refine GlobalTheory.T.tendsto_zero_of_open_set_linear_roots atTop (fun R => O.Y.arDeg (setB O.Y B) R - (show MvPolynomial (Rt D.what₂.Tau O.Y.N) ℝ →ₗ[ℝ] ℝ from (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x' O.Φ)).arDeg (setB O.Y B) R))
    _ {u | ∀ τ, StrictAnti (u τ)} ?_ ?_ ?_ v
  · have e : {u : D.what₂.Tau → Fin O.Y.N → ℝ | ∀ τ, StrictAnti (u τ)} =
        ⋂ τ, ⋂ a : Fin O.Y.N, ⋂ b : Fin O.Y.N, {u | a < b → u τ b < u τ a} := by
      ext u; simp [StrictAnti]
    rw [e]
    refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    by_cases hab : a < b
    · simpa [hab] using isOpen_lt ((continuous_apply b).comp (continuous_apply τ))
        ((continuous_apply a).comp (continuous_apply τ))
    · simp [hab]
  · exact ⟨fun _ i => -(i : ℝ), fun τ a b hab => by simpa using hab⟩
  · intro u hu
    have hR2 : ∀ R : ℝ, Real.exp 2 ≤ R → 2 ≤ R := fun R hR =>
      le_trans (by have := Real.add_one_le_exp 2; linarith) hR
    have hl := tendsto_finset_sum (Finset.univ : Finset O.Y.Comp) fun c _ =>
      tendsto_finset_sum (Finset.range (dimY O.Y + 1)) fun i hi =>
        GlobalTheory.T.tendsto_mixed_integral_difference_zero h2 hH D O hC hf A T H h x' B hB u hu c i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    simp only [Finset.sum_const_zero] at hl
    refine (tendsto_congr' ?_).2 hl
    filter_upwards [eventually_ge_atTop (Real.exp 2)] with R hR
    rw [LinearMap.sub_apply]
    change O.Y.arDeg (setB O.Y B) R (linRoot u ^ (dimY O.Y + 1)) -
      (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x' O.Φ)).arDeg (setB O.Y B) R (linRoot u ^ (dimY O.Y + 1)) = _
    rw [hT B hB R hR u, GlobalTheory.T.arithmetic_degree_linear_root_sum h2 hH D O hC hf A T H h x' B hB R hR u, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Real0.fR, zero_smul, add_zero]
    exact GlobalTheory.T.top_degree_difference_telescoping _ _ _ _ _ (hsm R (hR2 R hR) u c) (GlobalTheory.T.smooth_potential_truncation h2 hH D O hC hf A T H h x' R (hR2 R hR) u c)

end GlobalTheory.ArDegIndep
