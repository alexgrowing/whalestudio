import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselQuotientMassEqConstMulNormSqTranslates
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_l2SG_translates_eq_const_mul_norm_sq : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B : R.H → Wp) (w : R.H), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π B → w ∈ R.sm → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → ∃ c : ℝ, 0 ≤ c ∧ ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = ENNReal.ofReal (c * ‖v‖ ^ 2) := by
  first | exact @GlobalTheory.BesselIsometry.besselQuotientMass_eq_const_mul_norm_sq_translates | exact GlobalTheory.BesselIsometry.besselQuotientMass_eq_const_mul_norm_sq_translates | (intros; apply GlobalTheory.BesselIsometry.besselQuotientMass_eq_const_mul_norm_sq_translates <;> assumption)
