import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold

noncomputable section

namespace GlobalTheory.GaugeQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal

variable {P Q P' Q' : ℕ}

def hsDist (g : UpqT P Q) : ℝ := ∑ i, ∑ j, ‖(UpqT.mat g - 1) i j‖ ^ 2

def ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ ^ 2 + 2 * ∑ i, ‖y (e (some i))‖ ^ 2

def tanSq (t : ℝ × Sp P' Q') : ℝ := t.1 ^ 2 + 2 * ∑ i, ‖t.2 i‖ ^ 2

def gaussSp (y : Sp P Q) : ℝ := Real.exp (-∑ i, ‖y i‖ ^ 2)

def ballVol (d : ℕ) (r : ℝ) : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)

def HasEuclDensity (μ : Measure (UpqT P Q)) : Prop :=
  Tendsto (fun r : ℝ => μ {g | hsDist g < r ^ 2} / ballVol ((P + Q) ^ 2) r) (𝓝[>] 0) (𝓝 1)

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.hsDist_nonneg (g : _root_.Formalism.BasicNotions.UpqT P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.hsDist g := by
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_hsDist : Continuous (_root_.GlobalTheory.GaugeQuot.hsDist : _root_.Formalism.BasicNotions.UpqT P Q → ℝ) := by
  have hmat : Continuous (_root_.Formalism.BasicNotions.UpqT.mat : _root_.Formalism.BasicNotions.UpqT P Q → _) := _root_.GlobalTheory.UpqTopology.continuous_mat
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_apply j).comp ((continuous_apply i).comp
    (hmat.sub continuous_const))).norm).pow 2

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ptSq_nonneg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.ptSq e y := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (_root_.GlobalTheory.GaugeQuot.ptSq e) := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.tanSq_nonneg (t : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q') :
    0 ≤ _root_.GlobalTheory.GaugeQuot.tanSq t := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_tanSq :
    Continuous (_root_.GlobalTheory.GaugeQuot.tanSq : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q' → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_gaussSp :
    Continuous (_root_.GlobalTheory.GaugeQuot.gaussSp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.gaussSp
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_mul (d : ℕ) (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d (t * r) = ENNReal.ofReal (t ^ d) * _root_.GlobalTheory.GaugeQuot.ballVol d r := by
  unfold _root_.GlobalTheory.GaugeQuot.ballVol
  rw [Measure.addHaar_ball_mul_of_pos _ _ ht, finrank_euclideanSpace_fin]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_zero (d : ℕ) {r : ℝ} (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ 0 :=
  (Metric.measure_ball_pos volume _ hr).ne'

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_top (d : ℕ) (r : ℝ) : _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ ⊤ :=
  measure_ball_lt_top.ne

end GlobalTheory.GaugeQuot
