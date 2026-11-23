import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrRightOfFinite

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem adelic_unimodular_of_finite_covolume (X : CData) (hd : RegData X) (hV : X.FinVol) : UnimodA X := by
  obtain ⟨hH, hF, -⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  exact rr_right_of_finite (rr_FD_of X.I X.μf X.fund hF) hV

theorem UnimodF_of_UnimodA (X : CData) (h : UnimodA X) : UnimodF X := by
  have : (X.I.muA X.μf).IsMulRightInvariant := h
  refine ⟨fun g => ?_⟩
  set B : Set X.I.Ginf := Set.pi univ fun v => {y : Formalism.REAL.UJ (X.I.ε v) | Formalism.REAL.hsG y ≤ (X.I.n : ℝ) + 1} with hBdef
  have hB : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) B =
      ∏ v, Formalism.REAL.muG (X.I.ε v) {y : Formalism.REAL.UJ (X.I.ε v) | Formalism.REAL.hsG y ≤ (X.I.n : ℝ) + 1} := Measure.pi_pi _ _
  have hB0 : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) B ≠ 0 := by
    rw [hB]
    exact Finset.prod_ne_zero_iff.2 fun v _ => (Formalism.REAL.frobenius_ball_compact_pos_finite (X.I.ε v)).2.1.ne'
  have hBt : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.prod_ne_top fun v _ => (Formalism.REAL.frobenius_ball_compact_pos_finite (X.I.ε v)).2.2.ne
  ext A hA
  rw [Measure.map_apply (measurable_mul_const g) hA]
  have key : (X.I.muA X.μf) ((fun x : X.I.GA => x * ((1 : X.I.Ginf), g)) ⁻¹' (B ×ˢ A)) = (X.I.muA X.μf) (B ×ˢ A) :=
    measure_preimage_mul_right _ _ _
  have e1 : (fun x : X.I.GA => x * ((1 : X.I.Ginf), g)) ⁻¹' (B ×ˢ A) = B ×ˢ ((fun y => y * g) ⁻¹' A) := by
    ext ⟨a, b⟩
    simp
  rw [e1] at key
  unfold AutInst.muA at key
  rw [Measure.prod_prod, Measure.prod_prod] at key
  exact (ENNReal.mul_right_inj hB0 hBt).1 key

theorem regularRep_measurable_of_finite_volume (X : CData) (hd : RegData X) (hV : X.FinVol) : X.RegRep :=
  regularRep_isometric_weaklyMeasurable X hd (adelic_unimodular_of_finite_covolume X hd hV)

def KernelDiagonalVolumeModulusConditions (n₀ : ℕ) (A C cb c₁ A₂ cε C₁ : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.KernelDiag ∧ X.FinVol ∧
    ∃ Mod : Set X.I.GA, MeasurableSet Mod ∧ X.ProbMod c₁ Mod ∧
      X.NearStep (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) c₁ A₂ Mod ∧
      X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) Mod ∧ X.DeepInt (A₂ + 1) Mod

theorem kernel_conditions_iff_without_regular_rep (n₀ : ℕ) (A C cb c₁ A₂ cε C₁ : ℝ) :
    StepsC'' n₀ A C cb c₁ A₂ cε C₁ ↔ KernelDiagonalVolumeModulusConditions n₀ A C cb c₁ A₂ cε C₁ :=
  ⟨fun h X hX => (h X hX).2, fun h X hX =>
    ⟨regularRep_measurable_of_finite_volume X (RegData_of_HypB X hX.1) (h X hX).2.1, h X hX⟩⟩

end Formalism.MainNotions.LeviCoordinates

end
