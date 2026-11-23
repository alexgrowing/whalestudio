import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliLaws_coefficientFieldChange : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f : cuspW Xo c U (wtZ a n), ∃ h : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n), ∀ σ : c'.F →+* ℂ, normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ ⟨_, h⟩ = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ.comp (incF c c' hle)) f := by
  first | exact @GlobalTheory.LawsFieldChange.laws_fieldChange | exact GlobalTheory.LawsFieldChange.laws_fieldChange | (intros; apply GlobalTheory.LawsFieldChange.laws_fieldChange <;> assumption)
