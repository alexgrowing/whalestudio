import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareSizeBoundsAlongFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shareSize_bounds_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p0 : ℕ), p0 ≤ (Fm.D x ι).R.r → 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * (p0 * ((Fm.D x ι).R.r - p0))) + 2 ≤ (Fm.parT x hx ι).TO ∧ ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) * ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) + 6) / (Fm.parT x hx ι).TO ≤ 1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3)) := by
  first | exact @GlobalTheory.ShareNumbers.numbers_along_family | exact GlobalTheory.ShareNumbers.numbers_along_family | (intros; apply GlobalTheory.ShareNumbers.numbers_along_family <;> assumption)
