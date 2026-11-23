import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TwoSidedBoundOfPointwiseBounds
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PointEvaluationMultiplicativeTsum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.DerivSimilitudeCharAtOneEqTrace
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.SecondOrderTaylorRemainderBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceMomentIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianTraceFormEstimate
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem entry_le {E : Type} [Field E] [NumberField E] {a : ℕ} (M : Matrix (Fin a) (Fin a) (Cinf E))
    (i j : Fin a) (w : InfinitePlace E) : ‖M i j w‖ ≤ ‖toL M‖ :=
  (norm_le_pi_norm (toL M i j) w).trans ((norm_le_pi_norm (toL M i) j).trans (norm_le_pi_norm (toL M) i))

private theorem abs_trF_le {E : Type} [Field E] [NumberField E] {a : ℕ} (M p : Matrix (Fin a) (Fin a) (Cinf E)) :
    |trF M p| ≤ Fintype.card (InfinitePlace E) * (a * (a * (‖toL M‖ * ‖toL p‖))) := by
  unfold trF
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (a * (‖toL M‖ * ‖toL p‖))) ?_).trans (by simp)
  intro w _
  refine (Complex.abs_re_le_norm _).trans ?_
  have h : (M * p).trace w = ∑ i, ∑ j, M i j w * p j i w := by
    simp [Matrix.trace, Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (‖toL M‖ * ‖toL p‖)) ?_).trans (by simp)
  intro i _
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (‖toL M‖ * ‖toL p‖) ?_).trans (by simp)
  intro j _
  rw [norm_mul]
  exact mul_le_mul (entry_le M i j w) (entry_le p j i w) (norm_nonneg _) (norm_nonneg _)

private theorem trF_add_smul {E : Type} [Field E] [NumberField E] {a : ℕ} (M p p' : Matrix (Fin a) (Fin a) (Cinf E))
    (c : ℝ) : trF M (p + c • p') = trF M p + c * trF M p' := by
  unfold trF
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]
  simp

theorem UpperTheory.hermitian_trace_form_entry_estimate :
    FnTaylor := by
  intro E _ _ _ a ha L hL
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C₁, hC₁, hT⟩ := UpperTheory.two_sided_bound_of_pointwise_bounds N
  obtain ⟨C₂, ε₂, hC₂, hε₂, hS⟩ := UpperTheory.second_order_taylor_remainder_bound E a
  obtain ⟨-, ⟨B, hB, hBd⟩, -⟩ := UpperTheory.hermitian_trace_form_estimate E a ha L hL
  obtain ⟨hq1, hqa, hqh, hqc, hqb, -⟩ := UpperTheory.geometric_side_quadraticForm_identity E a
  obtain ⟨-, -, -, hsc, -⟩ := UpperTheory.deriv_similitudeChar_at_one_eq_trace E a
  set K : ℝ := C₂ + (1 + C₂) * a with hK
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hK0 : 0 ≤ K := by positivity
  set D : ℝ := ‖toL (1 : Matrix (Fin a) (Fin a) (Cinf E))‖ + 1 with hD
  have hD0 : 0 ≤ D := by positivity
  set n : ℝ := (Fintype.card (InfinitePlace E) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨C₁ * K ^ 2 + Real.pi * (C₂ * (n * (a * (a * (B * D))))), min ε₂ (min 1 (1 / (4 * (K + 1)))),
    by positivity, by positivity, ?_⟩
  intro g Y h hl hY hh
  set y := ‖toL Y‖ with hy
  have hy0 : 0 ≤ y := norm_nonneg _
  have hy2 : y ≤ ε₂ := hY.trans (min_le_left _ _)
  have hy1 : y ≤ 1 := hY.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hy3 : y ≤ 1 / (4 * (K + 1)) := hY.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKy : K * y ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hy3
    nlinarith only [hy3, hy0]
  have hs := hS Y hy2
  rw [hl, add_zero, ← hy] at hs
  set s := sc (1 + Y) with hsdef
  have hs1 : |s - 1| ≤ C₂ * y := hs.trans (mul_le_mul_of_nonneg_left (by nlinarith only [hy0, hy1]) hC₂)
  have hs2 : |s - 1| ≤ C₂ := hs1.trans (by nlinarith only [hy1, hC₂])
  have hs3 : |s| ≤ 1 + C₂ := by
    have := abs_le.1 hs2
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  set p := Y + (s - 1) • (1 + Y) with hp
  have hquad : ∀ x, quad p x = (s - 1) * qf x + s * quad Y x := by
    intro x
    rw [hp, (hqa _ _ 0 x).1, (hqa _ 0 (s - 1) x).2, (hqa _ _ 0 x).1, hq1]
    ring
  have hu : ∀ x, |quad p x| ≤ K * y * qf x := by
    intro x
    have hx := qf_nonneg x
    rw [hquad]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hx]
    have h1 : |s - 1| * qf x ≤ C₂ * y * qf x := mul_le_mul_of_nonneg_right hs1 hx
    have h2 : |s| * |quad Y x| ≤ (1 + C₂) * (a * y * qf x) :=
      mul_le_mul hs3 (hqb Y x) (abs_nonneg _) (by positivity)
    calc _ ≤ C₂ * y * qf x + (1 + C₂) * (a * y * qf x) := add_le_add h1 h2
      _ = K * y * qf x := by rw [hK]; ring
  haveI : Nonempty (lat L g) := ⟨0⟩
  have key := hT (lat L g) (fun v => qf (pt (rt g) v.1)) (fun v => quad p (pt (rt g) v.1)) (K * y) (hN g)
    (by positivity) hKy (fun v => hu _)
  have e1 : fn L (g * infGL E a h) =
      Real.log (∑' v : lat L g, Real.exp (-Real.pi * (qf (pt (rt g) v.1) + quad p (pt (rt g) v.1)))) := by
    unfold fn Th
    rw [(UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.1 g h]
    congr 1
    refine tsum_congr fun v => ?_
    unfold gauss
    rw [hqc, hqh, ← hsc h, hh, ← hsdef, hquad, (hqa _ _ 0 _).1, hq1]
    congr 2
    ring
  have e2 := UpperTheory.hermitian_space_moment_identity E a ha L hL g p
  have key' : |fn L (g * infGL E a h) - fn L g + Real.pi * trF (mom L g).1 p| ≤
      C₁ * (K * y) ^ 2 := by
    rw [e1, e2]
    exact key
  rw [hp, trF_add_smul] at key'
  have h1 : ‖toL (1 + Y)‖ ≤ D := by
    have : toL (1 + Y) = toL 1 + toL Y := rfl
    rw [this]
    exact (norm_add_le _ _).trans (by rw [hD]; linarith)
  have h2 : |trF (mom L g).1 (1 + Y)| ≤ n * (a * (a * (B * D))) := by
    refine (abs_trF_le _ _).trans ?_
    have := mul_le_mul (hBd g).1 h1 (norm_nonneg _) hB.le
    gcongr
  have h3 : |Real.pi * ((s - 1) * trF (mom L g).1 (1 + Y))| ≤
      Real.pi * (C₂ * y ^ 2 * (n * (a * (a * (B * D))))) := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hs h2 (abs_nonneg _) (by positivity)) Real.pi_pos.le
  have h4 := abs_le.1 key'
  have h5 := abs_le.1 h3
  rw [abs_le]
  constructor <;> linarith only [h4.1, h4.2, h5.1, h5.2]

end
