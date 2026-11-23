import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC.KN

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem memGL (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

def S2 (a : Mat n) : ℝ := ∑ i, ∑ j, ‖a i j‖ ^ 2

theorem schatten_two_nonneg (a : Mat n) : 0 ≤ S2 a := by
  unfold S2
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

theorem schatten_two_mul_le (a b : Mat n) : S2 (a * b) ≤ S2 a * S2 b := by
  unfold S2
  have key : ∀ i j, ‖(a * b) i j‖ ^ 2 ≤ (∑ k, ‖a i k‖ ^ 2) * (∑ k, ‖b k j‖ ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    calc ‖∑ k, a i k * b k j‖ ^ 2 ≤ (∑ k, ‖a i k‖ * ‖b k j‖) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          exact (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
      _ ≤ (∑ k, ‖a i k‖ ^ 2) * (∑ k, ‖b k j‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ∑ j, ‖(a * b) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖a i k‖ ^ 2) * (∑ k, ‖b k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖a i k‖ ^ 2) * (∑ j, ∑ k, ‖b k j‖ ^ 2) := by rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, ‖a i j‖ ^ 2) * (∑ i, ∑ j, ‖b i j‖ ^ 2) := by rw [Finset.sum_comm (f := fun j k => ‖b k j‖ ^ 2)]

theorem lg_eq (y : Mat n) : lg y = Real.log (1 + S2 y + S2 y⁻¹) := by
  unfold lg S2
  congr 1
  simp only [Finset.sum_add_distrib]
  ring

theorem lg_mul_le (a b : Mat n) : lg (a * b) ≤ lg a + lg b := by
  have h1 := schatten_two_mul_le a b
  have h2 := schatten_two_mul_le b⁻¹ a⁻¹
  have p1 := schatten_two_nonneg a
  have p2 := schatten_two_nonneg a⁻¹
  have p3 := schatten_two_nonneg b
  have p4 := schatten_two_nonneg b⁻¹
  have p5 := schatten_two_nonneg (a * b)
  have p6 := schatten_two_nonneg (b⁻¹ * a⁻¹)
  rw [lg_eq, lg_eq, lg_eq, ← Real.log_mul (by linarith) (by linarith), Matrix.mul_inv_rev]
  apply Real.log_le_log (by linarith)
  nlinarith [mul_nonneg p1 p3, mul_nonneg p1 p4, mul_nonneg p2 p3, mul_nonneg p2 p4]

theorem lg_inv (a : Mat n) (ha : a ∈ GLs n) : lg a⁻¹ = lg a := by
  have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  rw [lg_eq, lg_eq, Matrix.nonsing_inv_nonsing_inv a hu]
  ring_nf

theorem lg_le_of_mul (u y : Mat n) (hy : y ∈ GLs n) : lg u ≤ lg (u * y) + lg y := by
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hy
  have e : u = u * y * y⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  calc lg u = lg (u * y * y⁻¹) := congrArg lg e
    _ ≤ lg (u * y) + lg y⁻¹ := lg_mul_le _ _
    _ = lg (u * y) + lg y := by rw [lg_inv y hy]

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem lg_contOn : ContinuousOn lg (GLs n) := by
  intro y hy
  have hinv : ContinuousAt (fun x : Mat n => x⁻¹) y := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hy
  have hs : ContinuousAt (fun x : Mat n => 1 + ∑ a, ∑ b, (‖x a b‖ ^ 2 + ‖x⁻¹ a b‖ ^ 2)) y := by
    apply continuousAt_const.add
    apply tendsto_finset_sum
    intro a _
    apply tendsto_finset_sum
    intro b _
    have e1 : ContinuousAt (fun x : Mat n => x a b) y := (continuous_id.matrix_elem a b).continuousAt
    have e2 : ContinuousAt (fun x : Mat n => x⁻¹ a b) y :=
      ((continuous_id.matrix_elem a b).continuousAt).comp (f := fun x : Mat n => x⁻¹) hinv
    exact (e1.norm.pow 2).add (e2.norm.pow 2)
  apply ContinuousAt.continuousWithinAt
  unfold lg
  refine hs.log ?_
  have : 0 ≤ ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  linarith

end PositivityTheory.RgBcC.VC.KN
