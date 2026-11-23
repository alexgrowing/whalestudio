import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedActionAcrisTensorSubEventuallyLpow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallySubMemPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedAction_acrisTensor_sub_eventually_lpow : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l), Continuous s → ∀ (T : LocLat G ℚ_[l] K O), (∀ t ∈ T.L.T, ∀ m : ℕ, ∀ᶠ g in nhds (1 : G), ∃ t' ∈ T.L.T, T.ρ g t - t = ((l : O) ^ m) • t') → ∀ (β : TW (OCr l O) T) (m : ℕ), ∀ᶠ g in nhds (1 : G), ∃ γ : TW (OCr l O) T, TWact (galOCr O (s g)) T g β - β = ((l : O) ^ m) • γ := by
  first | exact @GlobalTheory.OCrCont.twact_sub_smul_eventually | exact GlobalTheory.OCrCont.twact_sub_smul_eventually | (intros; apply GlobalTheory.OCrCont.twact_sub_smul_eventually <;> assumption)
