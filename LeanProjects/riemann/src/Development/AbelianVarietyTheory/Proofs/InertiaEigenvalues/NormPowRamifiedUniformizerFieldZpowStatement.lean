import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKur
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocB
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_ramifiedUniformizerField_zpow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (y : Om l), y ∈ (ϖ.field a).1 → y ≠ 0 → ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  first | exact @GlobalTheory.ValGroupKprime.norm_pow_field | exact GlobalTheory.ValGroupKprime.norm_pow_field | (intros; apply GlobalTheory.ValGroupKprime.norm_pow_field <;> assumption)
