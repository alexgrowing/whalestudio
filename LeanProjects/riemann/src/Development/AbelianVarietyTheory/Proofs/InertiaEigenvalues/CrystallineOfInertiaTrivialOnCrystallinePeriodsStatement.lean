import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfInertiaTrivialOnCrystallinePeriods
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_of_inertia_trivial_on_crystallinePeriods : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' F : FinExt l), (GK K').Normal → ∀ T : QLat LL, IsCrys (Pl.PD K') (resF T K').ρ → ((∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), (g : GQ l) ∈ GK F → ∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → IsCrys (Pl.PD F) (resF T F).ρ) ∧ ∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∀ p : Polynomial ↥LL.1, (∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p x = 0) → ∀ x ∈ Dcris (Pl.PD F) (resF T F).ρ, Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p x = 0 := by
  first | exact @GlobalTheory.CrysInertDescent.main | exact GlobalTheory.CrysInertDescent.main | (intros; apply GlobalTheory.CrysInertDescent.main <;> assumption)
