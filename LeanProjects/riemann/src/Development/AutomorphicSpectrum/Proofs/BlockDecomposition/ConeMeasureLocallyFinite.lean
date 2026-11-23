import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceSingleMulSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTwistHomotopyKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeIsOpenStatement

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar.Fin

variable {n : ℕ}

theorem continuous_hOf : Continuous (hOf (n := n)) := by
  unfold hOf
  refine continuous_finset_sum _ fun p _ => ?_
  exact (Complex.continuous_ofReal.comp (continuous_apply p)).smul continuous_const

theorem continuous_detRe : Continuous fun v : Fin n × Fin n → ℝ => (hOf v).det.re :=
  Complex.continuous_re.comp (continuous_hOf.matrix_det)

theorem detRe_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : 0 < (hOf v).det.re := by
  have h : 0 < (hOf v).det := Matrix.PosDef.det_pos hv
  exact (Complex.pos_iff.1 h).1

theorem measurable_coneW : Measurable (coneW n) := by
  unfold coneW
  exact ENNReal.measurable_ofReal.comp ((continuous_detRe.measurable.pow_const n).inv)

theorem exists_hOf_eq_one : ∃ v : Fin n × Fin n → ℝ, hOf v = 1 := by
  refine ⟨fun p => ((1 * hb p : Mat n).trace).re, ?_⟩
  have hre : ∀ p : Fin n × Fin n, ((((1 * hb p : Mat n).trace).re : ℝ) : ℂ) = (1 * hb p : Mat n).trace := by
    intro p
    apply Complex.conj_eq_iff_re.1
    have h1 : star (hb p : Mat n).trace = (hb p : Mat n).trace := by
      rw [← Matrix.trace_conjTranspose, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]
    simpa using h1
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr (1 : Mat n)
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, hre]

theorem cone_nonempty : (cone n).Nonempty := by
  obtain ⟨v, hv⟩ := exists_hOf_eq_one (n := n)
  refine ⟨v, ?_⟩
  show (hOf v).PosDef
  rw [hv]
  exact Matrix.PosDef.one

theorem coneW_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : coneW n v ≠ 0 := by
  unfold coneW
  have : 0 < ((hOf v).det.re ^ n)⁻¹ := inv_pos.2 (pow_pos (detRe_pos hv) n)
  exact (ENNReal.ofReal_pos.2 this).ne'

theorem coneMeas_ne_zero : coneMeas n ≠ 0 := by
  intro h0
  have hz := (withDensity_eq_zero measurable_coneW.aemeasurable h0)
  have hopen : IsOpen (cone n) := GlobalTheory.T.positive_cone_isOpen n
  have hvol : 0 < volume (cone n) := hopen.measure_pos volume cone_nonempty
  rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet] at hz
  have hnull : volume (cone n) = 0 := by
    refine measure_mono_null (t := {v | ¬ (v ∈ cone n → coneW n v = (0 : (Fin n × Fin n → ℝ) → ℝ≥0∞) v)}) ?_ hz
    intro v hv
    simpa using ⟨hv, coneW_pos hv⟩
  exact hvol.ne' hnull

theorem coneMeas_lt_top (C : Set (Fin n × Fin n → ℝ)) (hC : IsCompact C) (hCc : C ⊆ cone n) :
    coneMeas n C < ⊤ := by
  have hcont : ContinuousOn (fun v : Fin n × Fin n → ℝ => ((hOf v).det.re ^ n)⁻¹) C :=
    ContinuousOn.inv₀ (continuous_detRe.pow n).continuousOn
      fun v hv => (pow_pos (detRe_pos (hCc hv)) n).ne'
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont
  have hle : ∀ v ∈ C, coneW n v ≤ ENNReal.ofReal M := fun v hv =>
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM v hv))
  unfold coneMeas
  rw [withDensity_apply _ hC.measurableSet]
  calc ∫⁻ v in C, coneW n v ∂(volume.restrict (cone n))
      ≤ ∫⁻ _ in C, ENNReal.ofReal M ∂(volume.restrict (cone n)) :=
        setLIntegral_mono' hC.measurableSet hle
    _ = ENNReal.ofReal M * (volume.restrict (cone n)) C := by simp
    _ ≤ ENNReal.ofReal M * volume C := by
        gcongr
        exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

theorem coneMeas_ne_zero_and_lt_top : ∀ n : ℕ, coneMeas n ≠ 0 ∧ ∀ C : Set (Fin n × Fin n → ℝ), IsCompact C →
    C ⊆ PositivityTheory.RgBcC.cone n → coneMeas n C < ⊤ :=
  fun _ => ⟨coneMeas_ne_zero, coneMeas_lt_top⟩

end GlobalTheory.CompanionTheory.ConeHaar.Fin
