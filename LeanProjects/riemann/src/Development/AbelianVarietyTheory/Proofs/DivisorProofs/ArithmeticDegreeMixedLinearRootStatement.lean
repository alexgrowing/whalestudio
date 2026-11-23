import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_degree_mixed_linear_root : ∀ (D : D7) (Y : DV.ShimX D.what₂.Tau) (T : Real0 Y), TieDeg T → ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, Real.exp 2 ≤ R →
    ∀ w u : Wt Y, Y.arDeg (GlobalTheory.FlagAr.setB Y B) R (Formalism.DegreeFormula.linRoot w * Formalism.DegreeFormula.linRoot u ^ Formalism.MainNotions.WeightThresholdDefs.dimY Y) =
      ∑ c, (T.K B c).num (Fin.cons (T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u)) := by
  first | exact @GlobalTheory.PolarDeg.arDeg_lin_mul_pow | exact GlobalTheory.PolarDeg.arDeg_lin_mul_pow | (intros; apply GlobalTheory.PolarDeg.arDeg_lin_mul_pow <;> assumption)
