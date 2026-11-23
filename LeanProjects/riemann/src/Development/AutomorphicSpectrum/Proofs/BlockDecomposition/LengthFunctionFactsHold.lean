import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq

noncomputable section

open Matrix Finset
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CompanionTheory.LengthGL

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hs (y : Mat n) : ℝ := ∑ a, ∑ b, ‖y a b‖ ^ 2

theorem hs_nonneg (y : Mat n) : 0 ≤ hs y :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

theorem lg_eq (y : Mat n) : lg y = Real.log (1 + (hs y + hs y⁻¹)) := by
  simp only [lg, hs, sum_add_distrib]

theorem hs_mul_le (x y : Mat n) : hs (x * y) ≤ hs x * hs y := by
  have h : ∀ a b, ‖(x * y) a b‖ ^ 2 ≤ (∑ c, ‖x a c‖ ^ 2) * ∑ c, ‖y c b‖ ^ 2 := by
    intro a b
    have h1 : ‖(x * y) a b‖ ≤ ∑ c, ‖x a c‖ * ‖y c b‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun c _ => norm_mul _ _))
    calc ‖(x * y) a b‖ ^ 2 ≤ (∑ c, ‖x a c‖ * ‖y c b‖) ^ 2 := by gcongr
      _ ≤ _ := sum_mul_sq_le_sq_mul_sq _ _ _
  calc hs (x * y) ≤ ∑ a, ∑ b, (∑ c, ‖x a c‖ ^ 2) * ∑ c, ‖y c b‖ ^ 2 :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => h a b
    _ = hs x * hs y := by
        simp only [hs, ← mul_sum, ← sum_mul]
        rw [sum_comm (f := fun b c => ‖y c b‖ ^ 2)]

theorem hs_eq_trace (y : Mat n) : hs y = (trace (y * yᴴ)).re := by
  have h : trace (y * yᴴ) = ((hs y : ℝ) : ℂ) := by
    simp only [trace, diag_apply, Matrix.mul_apply, conjTranspose_apply, hs, Complex.ofReal_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    simpa using Complex.mul_conj' (y a b)
  rw [h, Complex.ofReal_re]

theorem hs_left_unitary {k : Mat n} (hk : kᴴ * k = 1) (x : Mat n) : hs (k * x) = hs x := by
  rw [hs_eq_trace, hs_eq_trace, conjTranspose_mul, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hk, Matrix.mul_one]

theorem hs_right_unitary {k : Mat n} (hk : k * kᴴ = 1) (x : Mat n) : hs (x * k) = hs x := by
  rw [hs_eq_trace, hs_eq_trace, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k, hk, Matrix.one_mul]

def ent (a b : Fin n) : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)

theorem ent_apply (a b : Fin n) (y : Mat n) : ent a b y = y a b := rfl

theorem contDiff_ent (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) := (ent a b).contDiff

theorem contDiffOn_inv : ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹) (GLs n) :=
  ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero.restrict_scalars ℝ

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne.preimage (continuous_id.matrix_det (n := Fin n) (R := ℂ))

theorem contDiff_hs : ContDiff ℝ ∞ (hs : Mat n → ℝ) :=
  ContDiff.sum fun a _ => ContDiff.sum fun b _ => (contDiff_norm_sq ℝ).comp (contDiff_ent a b)

theorem phi_pos (y : Mat n) : 0 < 1 + (hs y + hs y⁻¹) := by
  have := hs_nonneg y
  have := hs_nonneg y⁻¹
  linarith

theorem contDiffOn_lg : ContDiffOn ℝ ∞ (lg : Mat n → ℝ) (GLs n) := by
  have hΦ : ContDiffOn ℝ ∞ (fun y : Mat n => 1 + (hs y + hs y⁻¹)) (GLs n) :=
    contDiffOn_const.add (contDiff_hs.contDiffOn.add (contDiff_hs.comp_contDiffOn contDiffOn_inv))
  exact (hΦ.log fun y _ => (phi_pos y).ne').congr fun y _ => lg_eq y

theorem sq_entry_le_hs (y : Mat n) (a b : Fin n) : ‖y a b‖ ^ 2 ≤ hs y :=
  calc ‖y a b‖ ^ 2 ≤ ∑ b, ‖y a b‖ ^ 2 :=
        single_le_sum (f := fun b => ‖y a b‖ ^ 2) (fun _ _ => by positivity) (mem_univ b)
    _ ≤ hs y := single_le_sum (f := fun a => ∑ b, ‖y a b‖ ^ 2)
        (fun _ _ => sum_nonneg fun _ _ => by positivity) (mem_univ a)

theorem mem_GLs_val (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isUnit_det_of_mem {x : Mat n} (hx : x ∈ GLs n) : IsUnit x.det := isUnit_iff_ne_zero.2 hx

theorem entry_le_of_lg_le {R : ℝ} {y : Mat n} (hy : lg y ≤ R) :
    (∀ a b, ‖y a b‖ ≤ Real.exp R) ∧ ∀ a b, ‖y⁻¹ a b‖ ≤ Real.exp R := by
  rw [lg_eq, Real.log_le_iff_le_exp (phi_pos y)] at hy
  have h1 := hs_nonneg y
  have h2 := hs_nonneg y⁻¹
  have key : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ Real.exp R → 1 ≤ Real.exp R → t ≤ Real.exp R := by
    intro t ht h h'
    by_contra hc
    push_neg at hc
    nlinarith
  have hE : 1 ≤ Real.exp R := by linarith
  exact ⟨fun a b => key _ (norm_nonneg _) ((sq_entry_le_hs y a b).trans (by linarith)) hE,
    fun a b => key _ (norm_nonneg _) ((sq_entry_le_hs y⁻¹ a b).trans (by linarith)) hE⟩

theorem isCompact_G (R : ℝ) : IsCompact {y : G n | lg y.val ≤ R} := by
  have hc : Continuous fun y : G n => lg y.val :=
    contDiffOn_lg.continuousOn.comp_continuous Units.continuous_val mem_GLs_val
  have hcl : IsClosed {y : G n | lg y.val ≤ R} := isClosed_le hc continuous_const
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper_real _
  have hB : IsCompact (Metric.closedBall (0 : Mat n) (Real.exp R)) := isCompact_closedBall _ _
  have hK : IsCompact ((Metric.closedBall (0 : Mat n) (Real.exp R)) ×ˢ
      (MulOpposite.op '' Metric.closedBall (0 : Mat n) (Real.exp R))) :=
    hB.prod (hB.image MulOpposite.continuous_op)
  have hpre := Units.isClosedEmbedding_embedProduct.isCompact_preimage hK
  refine hpre.of_isClosed_subset hcl fun y hy => ?_
  obtain ⟨h1, h2⟩ := entry_le_of_lg_le hy
  have hE : 0 ≤ Real.exp R := (Real.exp_pos R).le
  refine ⟨?_, ⟨(y⁻¹ : G n).val, ?_, rfl⟩⟩
  · simpa [Units.embedProduct] using (Matrix.norm_le_iff hE).2 h1
  · rw [mem_closedBall_zero_iff, Matrix.coe_units_inv]
    exact (Matrix.norm_le_iff hE).2 h2

theorem isCompact_Mat (R : ℝ) : IsCompact {y : Mat n | y ∈ GLs n ∧ lg y ≤ R} := by
  have e : {y : Mat n | y ∈ GLs n ∧ lg y ≤ R} = Units.val '' {y : G n | lg y.val ≤ R} := by
    ext y
    constructor
    · rintro ⟨hy, hl⟩
      obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det y).2 (isUnit_det_of_mem hy)
      exact ⟨u, hl, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨mem_GLs_val u, hu⟩
  rw [e]
  exact (isCompact_G R).image Units.continuous_val

theorem hasFDerivAt_hs (x : Mat n) : HasFDerivAt hs
    (∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (x a b)).comp (ent a b)) x := by
  refine HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => ?_
  exact (ent a b).hasFDerivAt.norm_sq

theorem fderiv_hs_sq_le (x v : Mat n) : (fderiv ℝ hs x v) ^ 2 ≤ 4 * hs x * hs v := by
  rw [(hasFDerivAt_hs x).fderiv]
  have h0 : (∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (x a b)).comp (ent a b)) v =
      2 * ∑ p ∈ univ ×ˢ univ, inner ℝ (x p.1 p.2) (v p.1 p.2) := by
    rw [sum_product, mul_sum]
    simp [ContinuousLinearMap.sum_apply, mul_sum, ent_apply, mul_add]
  rw [h0]
  have h1 : |∑ p ∈ (univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)), inner ℝ (x p.1 p.2) (v p.1 p.2)| ≤
      ∑ p ∈ (univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)), ‖x p.1 p.2‖ * ‖v p.1 p.2‖ :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => abs_real_inner_le_norm _ _)
  have h2 := sum_mul_sq_le_sq_mul_sq ((univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)))
    (fun p => ‖x p.1 p.2‖) (fun p => ‖v p.1 p.2‖)
  have e : ∀ y : Mat n, hs y = ∑ p ∈ (univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)), ‖y p.1 p.2‖ ^ 2 :=
    fun y => by rw [sum_product]; rfl
  rw [← e x, ← e v] at h2
  have h3 : (∑ p ∈ (univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)), inner ℝ (x p.1 p.2) (v p.1 p.2)) ^ 2 ≤
      hs x * hs v := by
    rw [← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans h2
  nlinarith

theorem hs_le_two (y w : Mat n) (h : hs w ≤ hs y) : |fderiv ℝ hs y w| ≤ 2 * hs y := by
  have h1 := fderiv_hs_sq_le y w
  have h2 := hs_nonneg y
  have h3 : (fderiv ℝ hs y w) ^ 2 ≤ (2 * hs y) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq h3 (by linarith)

theorem differentiableAt_inv {x : Mat n} (hx : x ∈ GLs n) :
    DifferentiableAt ℝ (fun y : Mat n => y⁻¹) x :=
  (contDiffOn_inv.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)

theorem fderiv_inv_mul {x : Mat n} (hx : x ∈ GLs n) (v : Mat n) :
    fderiv ℝ (fun y : Mat n => y⁻¹) x (x * v) = -(v * x⁻¹) := by
  set D := fderiv ℝ (fun y : Mat n => y⁻¹) x with hDdef
  have hD : HasFDerivAt (fun y : Mat n => y⁻¹) D x := (differentiableAt_inv hx).hasFDerivAt
  have key : ∀ w, x * D w + w * x⁻¹ = 0 := by
    intro w
    ext a b
    have h1 : HasFDerivAt (fun y : Mat n => ∑ c, y a c * y⁻¹ c b)
        (∑ c, (x a c • (ent c b).comp D + x⁻¹ c b • ent a c)) x :=
      HasFDerivAt.fun_sum fun c _ => (ent a c).hasFDerivAt.mul ((ent c b).hasFDerivAt.comp x hD)
    have h2 : (fun y : Mat n => ∑ c, y a c * y⁻¹ c b) =ᶠ[𝓝 x] fun _ => (1 : Mat n) a b := by
      filter_upwards [isOpen_GLs.mem_nhds hx] with y hy
      rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv y (isUnit_det_of_mem hy)]
    have h3 := h1.unique ((hasFDerivAt_const ((1 : Mat n) a b) x).congr_of_eventuallyEq h2)
    have h4 := congrArg (fun L : Mat n →L[ℝ] ℂ => L w) h3
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ent_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, sum_add_distrib] at h4
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply]
    rw [← h4]
    congr 1
    exact sum_congr rfl fun c _ => mul_comm _ _
  have h := key (x * v)
  have h5 : x⁻¹ * (x * D (x * v) + x * v * x⁻¹) = 0 := by rw [h, Matrix.mul_zero]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul x (isUnit_det_of_mem hx), Matrix.one_mul,
    Matrix.mul_assoc x, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul x (isUnit_det_of_mem hx), Matrix.one_mul] at h5
  exact eq_neg_of_add_eq_zero_left h5

theorem fderiv_lg_le {x : Mat n} (hx : x ∈ GLs n) {X : Mat n} (hX : hs X = 1) :
    |fderiv ℝ lg x (x * X)| ≤ 2 := by
  have hd : HasFDerivAt (fun y : Mat n => y⁻¹) (fderiv ℝ (fun y : Mat n => y⁻¹) x) x :=
    (differentiableAt_inv hx).hasFDerivAt
  have dh : ∀ y : Mat n, HasFDerivAt hs (fderiv ℝ hs y) y := fun y =>
    (contDiff_hs.differentiable (by simp) y).hasFDerivAt
  have hΦ : HasFDerivAt (fun y : Mat n => 1 + (hs y + hs y⁻¹))
      (fderiv ℝ hs x + (fderiv ℝ hs x⁻¹).comp (fderiv ℝ (fun y : Mat n => y⁻¹) x)) x :=
    ((dh x).add ((dh x⁻¹).comp x hd)).const_add 1
  have hl := hΦ.log (phi_pos x).ne'
  have hl2 := HasFDerivAt.congr_of_eventuallyEq (f₁ := (lg : Mat n → ℝ)) hl (Filter.Eventually.of_forall lg_eq)
  have hval : fderiv ℝ lg x (x * X) = (1 + (hs x + hs x⁻¹))⁻¹ * (fderiv ℝ hs x (x * X) +
      fderiv ℝ hs x⁻¹ (fderiv ℝ (fun y : Mat n => y⁻¹) x (x * X))) := by
    rw [hl2.fderiv]
    rfl
  rw [hval, fderiv_inv_mul hx X, map_neg]
  have hA : |fderiv ℝ hs x (x * X)| ≤ 2 * hs x :=
    hs_le_two _ _ (by simpa [hX] using hs_mul_le x X)
  have hB : |fderiv ℝ hs x⁻¹ (X * x⁻¹)| ≤ 2 * hs x⁻¹ :=
    hs_le_two _ _ (by simpa [hX] using hs_mul_le X x⁻¹)
  have hp := phi_pos x
  rw [abs_mul, abs_of_pos (inv_pos.2 hp), inv_mul_le_iff₀ hp]
  have h6 := abs_add_le (fderiv ℝ hs x (x * X)) (-fderiv ℝ hs x⁻¹ (X * x⁻¹))
  rw [abs_neg] at h6
  linarith

theorem hs_bs (p : Bool × Fin n × Fin n) : hs (bs p) = 1 := by
  obtain ⟨s, a, b⟩ := p
  have h : ∀ i j : Fin n, ‖bs (s, a, b) i j‖ ^ 2 = if a = i then (if b = j then 1 else 0) else 0 := by
    intro i j
    by_cases h1 : a = i <;> by_cases h2 : b = j <;> cases s <;> simp [bs, Matrix.single_apply, h1, h2]
  simp [hs, h]

theorem lg_mul_le (x y : Mat n) : lg (x * y) ≤ lg x + lg y := by
  rw [lg_eq, lg_eq, lg_eq, ← Real.log_mul (phi_pos x).ne' (phi_pos y).ne',
    Matrix.mul_inv_rev]
  refine Real.log_le_log (by have := hs_nonneg (x * y); have := hs_nonneg (y⁻¹ * x⁻¹); linarith) ?_
  have h1 := hs_mul_le x y
  have h2 := hs_mul_le y⁻¹ x⁻¹
  have a := hs_nonneg x
  have b := hs_nonneg x⁻¹
  have c := hs_nonneg y
  have d := hs_nonneg y⁻¹
  nlinarith [mul_nonneg a c, mul_nonneg a d, mul_nonneg b c, mul_nonneg b d]

theorem lg_inv {x : Mat n} (hx : x ∈ GLs n) : lg x⁻¹ = lg x := by
  rw [lg_eq, lg_eq, Matrix.nonsing_inv_nonsing_inv x (isUnit_det_of_mem hx), add_comm (hs x⁻¹)]

theorem lg_unitary (x : Mat n) (k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ) : lg (k₁.1 * x * k₂.1) = lg x := by
  have u₁ : k₁.1 * star k₁.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k₁.2
  have u₂ : k₂.1 * star k₂.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k₂.2
  have v₁ : star k₁.1 * k₁.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k₁.2
  have v₂ : star k₂.1 * k₂.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k₂.2
  have i₁ : k₁.1⁻¹ = star k₁.1 := Matrix.inv_eq_right_inv u₁
  have i₂ : k₂.1⁻¹ = star k₂.1 := Matrix.inv_eq_right_inv u₂
  have s₁ : (star k₁.1)ᴴ = k₁.1 := conjTranspose_conjTranspose _
  have s₂ : (star k₂.1)ᴴ = k₂.1 := conjTranspose_conjTranspose _
  rw [lg_eq, lg_eq, Matrix.mul_inv_rev, Matrix.mul_inv_rev, i₁, i₂,
    hs_right_unitary (k := k₂.1) u₂, hs_left_unitary (k := k₁.1) v₁,
    hs_left_unitary (k := star k₂.1) (by rw [s₂]; exact u₂),
    hs_right_unitary (k := star k₁.1) (by rw [s₁]; exact v₁)]

theorem lgFacts : LgFacts := fun n =>
  ⟨fun x _ y _ => lg_mul_le x y, fun _ hx => lg_inv hx, fun x _ k₁ k₂ => lg_unitary x k₁ k₂,
    contDiffOn_lg, isCompact_G, isCompact_Mat, 2, fun _ hx p => fderiv_lg_le hx (hs_bs p)⟩

end GlobalTheory.CompanionTheory.LengthGL
