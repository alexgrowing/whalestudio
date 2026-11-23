import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersRoundedSizeBoundWindowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxNonThickSizeShiftedValueAndBoundsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbeddingStatement

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_box : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → (pageWord L j ε τ φ).Box := by
  intro D L C j ε τ φ hR
  have hb := (GlobalTheory.T.roundedSizeBound_window L C hR).1
  have hw := (GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C hR).2.2
  have hnt := fun g => GlobalTheory.T.floor_size_bounds_not_thick_embedding L C g j hR
  have hth := fun g => GlobalTheory.T.floor_size_bounds_at_thick_embedding L g j
  obtain ⟨hC, h100, hroom, hwb, -, hCb⟩ := hR
  have hη := L.etaSz_pos
  have hS := L.Sc_pos
  have ht := L.t_win.1
  have ht' : 1 ≤ D.R.t := by exact_mod_cast ht
  have hLw : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : 0 ≤ L.sc.b' := by linarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by
    have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hb'
    linarith
  have hw0 : (0 : ℝ) ≤ wHat D := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
  have hE : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold etaHat
    push_cast
    have := Nat.floor_le hη.le
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ bHat L
    have : (1 : ℝ) ≤ bHat L := by linarith
    exact_mod_cast this
  · show 1 ≤ wHat D
    unfold wHat
    omega
  · show 20 * wHat D ≤ bHat L
    have : (20 : ℝ) * wHat D ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * etaHat L ≤ bHat L
    have : (20 : ℝ) * etaHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * sHat L ≤ bHat L
    have : (20 : ℝ) * sHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · intro i
    show ((etaHat L : ℕ) : ℤ) < szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))
    generalize letter τ φ i = g
    have hsz : L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) := by
      by_cases hT : Thick D.host g
      · have := (hth g hT).1
        linarith
      · exact (hnt g hT).1
    have key : ((etaHat L : ℕ) : ℤ) + D.R.t + 1 < ⌊(hcAt D g).e j⌋ := by
      have : ((etaHat L : ℕ) : ℝ) + D.R.t + 1 < (⌊(hcAt D g).e j⌋ : ℝ) := by linarith
      exact_mod_cast this
    unfold szT
    split_ifs <;> omega

end GlobalTheory.HTW
