import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

def ClosedSubgroupsStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ),
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (UH (Hpk k r)) ∧
      Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (Nset k r) ∧
      (inWb k r z → 0 < Tz k r z →
        Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (UWset k r z) ∧
          Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (Sset k r z))

def HaarUniq2Statement : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ ν : Measure (Mt k r)),
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) U →
    Formalism.MainNotions.S.IsHaarOn U μ → Formalism.MainNotions.S.IsHaarOn U ν → ∃ c : ℝ≥0, 0 < c ∧ ν = c • μ

def HaarMapStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P →
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r))
      ((Formalism.REAL.muG ε).map (fun g : Formalism.REAL.UJ ε => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)))

def SchurBStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (μG : Measure (Mt k r)),
    Formalism.MainNotions.S.IsDSHpk k r ε lam σ → Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG →
    Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ ∧ ∃ d : ℝ, S0.IsFdegB μG σ d

def QuotScaleStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS μW μN ν : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN →
    Formalism.MainNotions.S.IsHaarOn (Sset k r z) μS → Formalism.MainNotions.S.IsQuotMeas μG μS ν →
    ∃ c : ℝ≥0, 0 < c ∧
      Formalism.MainNotions.S.IsQuotMeas μG (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.muSL μW μN) ((c : ℝ≥0∞) • ν)

def ScaleNuStatement : Prop :=
  ∀ (k r : ℕ) (Vp : Type) [NormedAddCommGroup Vp] (ν : Measure (Mt k r)) (c : ℝ≥0) (W : Mat k r → Vp),
    Formalism.MainNotions.S.l2SG ((c : ℝ≥0∞) • ν) W = (c : ℝ≥0∞) * Formalism.MainNotions.S.l2SG ν W ∧
      (0 < c → (AEStronglyMeasurable (fun x => W (Matrix.of x)) ((c : ℝ≥0∞) • ν) ↔
        AEStronglyMeasurable (fun x => W (Matrix.of x)) ν))

end ReciprocityTheory.ChartRestriction.DS.Lap
