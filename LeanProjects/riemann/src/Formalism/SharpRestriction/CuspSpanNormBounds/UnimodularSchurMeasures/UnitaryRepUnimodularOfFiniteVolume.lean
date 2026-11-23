import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RegularRepAlgebraicMeasurableContinuous
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrdStronglyMeasurable

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem adelic_regular_rep_unitary_continuous (X : CData) (hd : RegData X) (hu : UnimodA X) (hl : LocFinF X) : RepA X := by
  have hH : X.μf.IsHaarMeasure := hd.1
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : SecondCountableTopology X.L2 := automorphic_L2_secondCountable X
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have : IsLocallyFiniteMeasure (X.I.muA X.μf) := rr_muA_locFin X hl
  have : (X.I.muA X.μf).IsOpenPosMeasure := rr_muA_openPos X
  have hne : X.I.muA X.μf ≠ 0 := fun h0 =>
    isOpen_univ.measure_ne_zero (X.I.muA X.μf) (univ_nonempty (α := X.I.GA))
      (by rw [h0, Measure.coe_zero, Pi.zero_apply])
  obtain ⟨h1, h2, h3⟩ := rightRegular_isometric_multiplicative X hd hu
  exact ⟨h1, h2, h3, fun F => rr_cont_of_meas' (μ := X.I.muA X.μf) hne h1 h2 h3 (regular_rep_coeff_measurable X hd hu) F⟩

theorem unitary_rep_of_finite_adelic_unimodular (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hu : UnimodF X) (h1 : X.e 1 ≠ 0) : RepA X :=
  adelic_regular_rep_unitary_continuous X (RegData_of_HypB X hX) (UnimodA_of_UnimodF X hu) (LocFinF_of_e X hX h1)

theorem unitary_rep_unimodular_of_finite_volume (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hV : X.FinVol) (h1 : X.e 1 ≠ 0) :
    RepA X ∧ UnimodF X :=
  have hd := RegData_of_HypB X hX
  have ha := adelic_unimodular_of_finite_covolume X hd hV
  ⟨adelic_regular_rep_unitary_continuous X hd ha (LocFinF_of_e X hX h1), UnimodF_of_UnimodA X ha⟩

theorem projection_count_cusp_of_unimodular {n₀ : ℕ} {A C : ℝ}
    (hred : ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → RepA X → UnimodF X → X.ProjStep ∧ X.CountedStep ∧ X.CuspStep)
    (hu : ∀ X : CData, X.HypB n₀ A → UnimodF X) : StepsB n₀ A C := by
  intro X hX t1 t2
  by_cases h1 : X.e 1 = 0
  · exact projection_count_cusp_of_trivial_idempotent X hX h1
  · exact hred X hX t1 t2 (unitary_rep_of_finite_adelic_unimodular X hX (hu X hX) h1) (hu X hX)

theorem projection_count_cusp_of_finite_volume {n₀ : ℕ} {A C : ℝ}
    (hred : ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → RepA X → UnimodF X → X.ProjStep ∧ X.CountedStep ∧ X.CuspStep)
    (hV : ∀ X : CData, X.HypB n₀ A → X.FinVol) : StepsB n₀ A C :=
  projection_count_cusp_of_unimodular hred fun X hX =>
    UnimodF_of_UnimodA X (adelic_unimodular_of_finite_covolume X (RegData_of_HypB X hX) (hV X hX))

end Formalism.MainNotions.LeviCoordinates

end
