import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.badShareSize_bounds_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ), Fm.x1 < x → x0 ≤ x → ∀ (ι : Fm.Ix x), 100 ≤ (Fm.D x ι).R.r ∧ TieAdmG (Fm.D x ι) ∧ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) ≤ 1 / 4 ∧ ∀ k : Fin 2, 2 ^ 12 ≤ (Fm.D x ι).host.g k ∧ 4 * (3 * ((Fm.D x ι).R.f : ℝ) / ((Fm.D x ι).host.g k : ℝ) + 23 * ((Fm.D x ι).R.f : ℝ) * Real.log ((Fm.D x ι).host.g k : ℝ) / Real.sqrt ((Fm.D x ι).host.g k : ℝ) + 2 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.m : ℝ) * (1 / (4 * ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ)) + (1 + Real.log ((Fm.D x ι).R.r : ℝ)) / (((Fm.D x ι).host.g k : ℝ) - 1)) + ((Fm.D x ι).R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ (Fm.D x ι).R.f + Real.exp (-((Fm.D x ι).R.f : ℝ) / (5 * Real.log ((Fm.D x ι).R.r : ℝ)))) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  first | exact @GlobalTheory.BadNumOnto.badShare_numbers_onto | exact GlobalTheory.BadNumOnto.badShare_numbers_onto | (intros; apply GlobalTheory.BadNumOnto.badShare_numbers_onto <;> assumption)
