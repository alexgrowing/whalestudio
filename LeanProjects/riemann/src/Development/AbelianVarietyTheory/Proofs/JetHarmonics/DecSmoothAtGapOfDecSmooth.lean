import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SideNormalisedGap
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.LieMatrixVectors
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.KFinDecayOfDecInf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SigmaFiniteOfPosLintegralNeTop

noncomputable section

namespace GlobalTheory.SideCompare

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open PI.BesselPeriodGGP (IsHaarOn IsQuotMeas)
open Formalism.FourierDecayAlt GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp decConst dimV dimN thrG thrS thrSS propExp DecGap Size Thresholds muS mulP IsSide
  IsSideNormalised KFinDecay wordSeminorm DecKFin DecSmooth)

theorem aOf_eq (r : ℕ) (h : ℝ) : ThreeDimData.aOf r h = decExp r h := rfl

theorem AG_eq (k r : ℕ) : ThreeDimData.AG k r = thrG k r := rfl

theorem dN_eq (k r : ℕ) : ThreeDimData.dN k r = dimN k r := rfl

theorem AS_eq (k r : ℕ) : ThreeDimData.AS k r = thrS k r := by
  unfold ThreeDimData.AS thrS dimV
  rw [dN_eq]; push_cast; ring

theorem Mexp_eq (r : ℕ) : ThreeDimData.Mexp r = propExp r := rfl

theorem dimV_eq (k r : ℕ) : ((2 * r + k + 1 : ℕ) : ℝ) = dimV k r := by
  unfold dimV; push_cast; ring

theorem decGap_of_cube (k r : ℕ) (h : ℝ) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) : DecGap k r h := by
  have := GapSizeCheck.decay_range k r h hh
  unfold DecGap
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  rw [← dimV_eq, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hr, Real.rpow_one, ← Real.sqrt_eq_rpow]
  exact this

theorem thresholds_of_gapOK (k r : ℕ) (h : ℝ) (hg : ThreeDimData.GapOK k r h) :
    DecGap k r h ∧ Thresholds k r (decExp r h) ∧ Thresholds k r (decExp r h - 1) := by
  obtain ⟨h1, h2, h3⟩ := GapSizeCheck.thresholds k r h hg
  rw [aOf_eq, AG_eq] at h1
  rw [aOf_eq, AS_eq] at h2
  rw [aOf_eq, AS_eq, AG_eq, Mexp_eq] at h3
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hg.1
  have hG : 4 ≤ thrG k r := by unfold thrG; nlinarith [mul_nonneg hr hr]
  refine ⟨decGap_of_cube k r h hg.2.1, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> (try unfold thrSS) <;> linarith

theorem sigmaFinite_of_isQuotMeas {k r : ℕ} {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS]
    (hS : μS ≠ 0) (hq : IsQuotMeas μG μS ν) : SigmaFinite ν := by
  first
  | (rename_i h_5 h_6; revert k r μG μS ν h_5 h_6 hS hq; exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas)
  | exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | (apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas ..)

theorem muS_ne_zero {k r : ℕ} {μW μN : Measure (Mt k r)} [SFinite μN] (hW : μW ≠ 0) (hN : μN ≠ 0) :
    muS μW μN ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero] at *
  unfold muS
  rw [Measure.map_apply SideNormalisedGap.measurable_mulP MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod]
  exact mul_ne_zero hW hN

section Side

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
  (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
  (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r))

end Side

section Decay

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def LowDecay (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ w₁ w₂ : H, IsLowUnitH k r ε lam σ w₁ → IsLowUnitH k r ε lam σ w₂ →
    ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ C * gN x ^ (-a)

def SmoothDecay (k r : ℕ) (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v₀ : H, IsKFinHpk (k := k) (r := r) σ v₀ →
    ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ D ∈ Ws, ∀ X ∈ D, InLieHpk k r X) ∧
      ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
        ‖⟪v₀, σ x w⟫_ℂ‖ ≤ C * wordSeminorm σ Ws w * gN x ^ (1 - a)

end Decay

def DecLowWeak : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → 120 * dimV k r ^ 3 ≤ h →
    LowDecay k r ε lam σ (decExp r h)

def DecSmoothAtGap : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → ThreeDimData.GapOK k r h →
    KFinDecay k r σ (decExp r h) → SmoothDecay k r σ (decExp r h)

end GlobalTheory.SideCompare
