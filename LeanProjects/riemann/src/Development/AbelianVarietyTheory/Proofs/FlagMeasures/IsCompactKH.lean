import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

instance borelMat (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))

def IsHaarKH (k r : ℕ) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ μ (GlobalTheory.ThA.KH k r)ᶜ = 0 ∧
    (∀ a ∈ GlobalTheory.ThA.KH k r, μ.map (fun g => a * g) = μ) ∧
    ∀ U : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsOpen U → 1 ∈ U → 0 < μ U

def peak (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := (1 + (Matrix.trace g).re / n) / 2

def peakN {n : ℕ} (μ : Measure (Matrix (Fin n) (Fin n) ℂ)) (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((peak n g ^ m / ∫ h, peak n h ^ m ∂μ : ℝ) : ℂ)

end GlobalTheory.KFinAvg

namespace GlobalTheory.KFinAvg
open Matrix

theorem isCompact_KH (k r : ℕ) : IsCompact (GlobalTheory.ThA.KH k r) := by
  have hc : IsClosed (PI.UpqRep.UH (PI.UpqRep.Hpk k r)) := by
    show IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact (GlobalTheory.isCompact_unitaryGroup (Fin (2 * r + k + 1)) ℂ).inter_left hc

end GlobalTheory.KFinAvg
