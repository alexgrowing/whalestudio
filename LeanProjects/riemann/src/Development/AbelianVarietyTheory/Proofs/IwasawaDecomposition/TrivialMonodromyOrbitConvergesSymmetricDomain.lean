import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDifferentiableOnTorsSq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

open GlobalTheory.ShFam.BdArc Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ShFam.OrbitLimit

theorem eventually_imTop (T : ℝ) : ∀ᶠ w in imTop, T < w.im :=
  (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)

instance imTop_neBot : imTop.NeBot :=
  comap_neBot fun t ht => by
    obtain ⟨y, hy⟩ := Filter.nonempty_of_mem ht
    exact ⟨y * Complex.I, by simpa using hy⟩

theorem exists_tendsto_norm_lt {T h c : ℝ} (hh : 0 < h) {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {w | T < w.im})
    (hp : ∀ w : ℂ, T < w.im → f (w + h) = f w) (hb : ∀ w : ℂ, T < w.im → ‖f w‖ < c) :
    ∃ L, Tendsto f imTop (𝓝 L) ∧ ‖L‖ < c := by
  classical
  let g : ℂ → ℂ := fun w => if T < w.im then f w else 0
  have hg : ∀ w : ℂ, T < w.im → g w = f w := fun w hw => if_pos hw
  have hgp : Function.Periodic g h := fun w => by
    by_cases hw : T < w.im
    · rw [hg w hw, hg _ (by simpa using hw), hp w hw]
    · simp [g, hw]
  have ho : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hgd : ∀ w : ℂ, T < w.im → DifferentiableAt ℂ g w := fun w hw =>
    (hd.congr fun z hz => hg z hz).differentiableAt (ho.mem_nhds hw)
  have hhol : ∀ᶠ w in imTop, DifferentiableAt ℂ g w := (eventually_imTop T).mono hgd
  have hbd : BoundedAtFilter imTop g := by
    refine Asymptotics.IsBigO.of_bound c ((eventually_imTop T).mono fun w hw => ?_)
    rw [hg w hw]
    simpa using (hb w hw).le
  set F := Function.Periodic.cuspFunction h g with hF
  set r : ℝ := Real.exp (-2 * Real.pi * (T + 1) / h) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have him : ∀ q : ℂ, q ≠ 0 → ‖q‖ ≤ r → T < (Function.Periodic.invQParam h q).im := fun q hq hqr => by
    rw [← Function.Periodic.norm_qParam_lt_iff hh, Function.Periodic.qParam_right_inv hh.ne' hq]
    refine hqr.trans_lt (Real.exp_lt_exp.2 ?_)
    rw [div_lt_div_iff_of_pos_right hh]
    nlinarith [Real.pi_pos]
  have hFd : DifferentiableOn ℂ F (closure (Metric.ball 0 r)) := fun q hq => by
    rw [closure_ball _ hr0.ne', mem_closedBall_zero_iff] at hq
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hq0 : q = 0
    · rw [hq0]
      exact Function.Periodic.differentiableAt_cuspFunction_zero hh hgp hhol hbd
    · rw [← Function.Periodic.qParam_right_inv hh.ne' hq0]
      exact Function.Periodic.differentiableAt_cuspFunction hh.ne' hgp (hgd _ (him q hq0 hq))
  refine ⟨F 0, (Function.Periodic.tendsto_at_I_inf hh hgp hhol hbd).congr' ((eventually_imTop T).mono hg), ?_⟩
  obtain ⟨z, hz, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm (f := F) Metric.isBounded_ball
    (Metric.nonempty_ball.2 hr0) hFd.diffContOnCl
  rw [frontier_ball _ hr0.ne', mem_sphere_zero_iff_norm] at hz
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz; exact hr0.ne hz
  have h1 : ‖F 0‖ ≤ ‖F z‖ := hmax (subset_closure (Metric.mem_ball_self hr0))
  refine h1.trans_lt ?_
  rw [hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hz0, hg _ (him z hz0 hz.le)]
  exact hb _ (him z hz0 hz.le)

def nsq {n : ℕ} (u : Fin n → ℂ) : ℝ := ∑ a, ‖u a‖ ^ 2

theorem nsq_nonneg {n : ℕ} (u : Fin n → ℂ) : 0 ≤ nsq u := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nsq_lim_lt {n : ℕ} {T h c : ℝ} (hh : 0 < h) {u : ℂ → Fin n → ℂ}
    (hd : ∀ a, DifferentiableOn ℂ (fun w => u w a) {w | T < w.im})
    (hp : ∀ w : ℂ, T < w.im → u (w + h) = u w) (hb : ∀ w : ℂ, T < w.im → nsq (u w) < c) {L : Fin n → ℂ}
    (hL : ∀ a, Tendsto (fun w => u w a) imTop (𝓝 (L a))) : nsq L < c := by
  obtain ⟨l, hl, hlt⟩ := exists_tendsto_norm_lt (c := (nsq L + c) / 2) hh
    (f := fun w => ∑ a, (starRingEnd ℂ) (L a) * u w a)
    (DifferentiableOn.fun_sum fun a _ => (hd a).const_mul _) (fun w hw => by simp only [hp w hw]) fun w hw => by
      refine (norm_sum_le _ _).trans_lt (lt_of_le_of_lt (b := (nsq L + nsq (u w)) / 2) ?_ (by linarith [hb w hw]))
      rw [nsq, nsq, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖L a‖ - ‖u w a‖)]
  have h2 := tendsto_nhds_unique hl (tendsto_finsetSum _ fun a _ => (hL a).const_mul ((starRingEnd ℂ) (L a)))
  have h3 : l = (nsq L : ℝ) := by
    rw [h2, nsq]
    push_cast
    exact Finset.sum_congr rfl fun a _ => Complex.conj_mul' _
  rw [h3, Complex.norm_real, Real.norm_of_nonneg (nsq_nonneg L)] at hlt
  linarith

def Jm (N p : ℕ) : Matrix (Fin N) (Fin N) ℂ := diagonal fun a : Fin N => ((sgn p (a : ℕ) : ℝ) : ℂ)

theorem sum_castLE {N p : ℕ} (hp : p ≤ N) {R : Type} [AddCommMonoid R] (f : Fin N → R) :
    ∑ j, f (Fin.castLE hp j) = ∑ a : Fin N, if (a : ℕ) < p then f a else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => Fin.castLE hp j) (fun j _ => by simp) (fun a _ b _ h => Fin.castLE_injective hp h)
    (fun a ha => ⟨⟨a, by simpa using ha⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl

theorem form_eq {N p : ℕ} (hp : p ≤ N) (u : Fin N → ℂ) :
    star u ⬝ᵥ Jm N p *ᵥ u = ((2 * nsq (fun j => u (Fin.castLE hp j)) - nsq u : ℝ) : ℂ) := by
  rw [nsq, nsq, sum_castLE hp (fun a => ‖u a‖ ^ 2), Finset.mul_sum, ← Finset.sum_sub_distrib, Complex.ofReal_sum,
    dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Jm, mulVec_diagonal, mul_left_comm, Pi.star_apply, Complex.star_def, Complex.conj_mul', sgn]
  split_ifs <;> push_cast <;> ring

theorem posDef_iff {N p : ℕ} (hp : p ≤ N) (U : Matrix (Fin N) (Fin p) ℂ) :
    (Uᴴ * Jm N p * U).PosDef ↔
      ∀ v, v ≠ 0 → nsq (U *ᵥ v) < 2 * nsq (U.submatrix (Fin.castLE hp) id *ᵥ v) := by
  have hH : (Uᴴ * Jm N p * U).IsHermitian := by
    refine isHermitian_conjTranspose_mul_mul _ ?_
    rw [Jm, IsHermitian, diagonal_conjTranspose]
    congr 1
    funext a
    simp
  have key : ∀ v, star v ⬝ᵥ (Uᴴ * Jm N p * U) *ᵥ v =
      ((2 * nsq (U.submatrix (Fin.castLE hp) id *ᵥ v) - nsq (U *ᵥ v) : ℝ) : ℂ) := fun v => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, form_eq hp]
    rfl
  rw [posDef_iff_dotProduct_mulVec, and_iff_right hH]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rw [key, Complex.zero_lt_real, sub_pos]

theorem det_top_ne {N p : ℕ} (hp : p ≤ N) {U : Matrix (Fin N) (Fin p) ℂ} (hU : (Uᴴ * Jm N p * U).PosDef) :
    (U.submatrix (Fin.castLE hp) id).det ≠ 0 := fun h0 => by
  obtain ⟨v, hv, h1⟩ := exists_mulVec_eq_zero_iff.2 h0
  have h2 := (posDef_iff hp U).1 hU v hv
  rw [h1] at h2
  have h3 := nsq_nonneg (U *ᵥ v)
  simp [nsq] at h2 h3
  linarith

def IsGraph {N p : ℕ} (hp : p ≤ N) (Y : Matrix (Fin N) (Fin p) ℂ) : Prop :=
  Y.submatrix (Fin.castLE hp) id = 1 ∧ (Yᴴ * Jm N p * Y).PosDef

theorem IsGraph.nsq_lt {N p : ℕ} {hp : p ≤ N} {Y : Matrix (Fin N) (Fin p) ℂ} (h : IsGraph hp Y) {v : Fin p → ℂ}
    (hv : v ≠ 0) : nsq (Y *ᵥ v) < 2 * nsq v := by
  have := (posDef_iff hp Y).1 h.2 v hv
  rwa [h.1, one_mulVec] at this

theorem isGraph_mul_inv {N p : ℕ} (hp : p ≤ N) {U : Matrix (Fin N) (Fin p) ℂ} (hU : (Uᴴ * Jm N p * U).PosDef) :
    IsGraph hp (U * (U.submatrix (Fin.castLE hp) id)⁻¹) := by
  have hd := (det_top_ne hp hU).isUnit
  refine ⟨?_, ?_⟩
  · rw [← mul_nonsing_inv _ hd]
    rfl
  · have := hU.conjTranspose_mul_mul_same (B := (U.submatrix (Fin.castLE hp) id)⁻¹)
      (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ hd)))
    simpa only [conjTranspose_mul, Matrix.mul_assoc] using this

theorem graph_limit {N p : ℕ} (hp : p ≤ N) {T h : ℝ} (hh : 0 < h) {Y : ℂ → Matrix (Fin N) (Fin p) ℂ}
    (hd : ∀ a j, DifferentiableOn ℂ (fun w => Y w a j) {w | T < w.im})
    (hper : ∀ w : ℂ, T < w.im → Y (w + h) = Y w) (hG : ∀ w : ℂ, T < w.im → IsGraph hp (Y w)) :
    ∃ Y₀, IsGraph hp Y₀ ∧ ∀ a j, Tendsto (fun w => Y w a j) imTop (𝓝 (Y₀ a j)) := by
  have hex : ∀ a j, ∃ L, Tendsto (fun w => Y w a j) imTop (𝓝 L) := fun a j => by
    obtain ⟨L, hL, -⟩ := exists_tendsto_norm_lt (c := 2) hh (hd a j) (fun w hw => by simp only [hper w hw])
      fun w hw => by
        have h1 := (hG w hw).nsq_lt (v := Pi.single j 1) (by simp)
        have h2 : nsq (Pi.single j (1 : ℂ) : Fin p → ℂ) = 1 := by
          rw [nsq, Finset.sum_eq_single j] <;> simp +contextual
        have h3 : ‖Y w a j‖ ^ 2 ≤ nsq (Y w *ᵥ Pi.single j 1) := by
          have := Finset.single_le_sum (f := fun a => ‖(Y w *ᵥ Pi.single j 1) a‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
          simpa [nsq] using this
        nlinarith [norm_nonneg (Y w a j)]
    exact ⟨L, hL⟩
  choose Y₀ hY using hex
  have h1 : (Matrix.of Y₀).submatrix (Fin.castLE hp) id = 1 := by
    ext i j
    refine tendsto_nhds_unique (hY (Fin.castLE hp i) j) (tendsto_const_nhds.congr' ((eventually_imTop T).mono ?_))
    intro w hw
    exact (congrFun (congrFun (hG w hw).1 i) j).symm
  refine ⟨Matrix.of Y₀, ⟨h1, (posDef_iff hp _).2 fun v hv => ?_⟩, hY⟩
  rw [h1, one_mulVec]
  refine nsq_lim_lt (T := T) hh (u := fun w => Y w *ᵥ v) (fun a => ?_) (fun w hw => by simp only [hper w hw])
    (fun w hw => (hG w hw).nsq_lt hv) fun a => ?_
  · exact DifferentiableOn.fun_sum (u := Finset.univ) fun j _ => (hd a j).mul_const (v j)
  · exact tendsto_finsetSum Finset.univ fun j _ => (hY a j).mul_const (v j)

def extend {N p : ℕ} (Y : Matrix (Fin N) (Fin p) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => if h : (b : ℕ) < p then Y a ⟨b, h⟩ else (1 : Matrix (Fin N) (Fin N) ℂ) a b

theorem extend_submatrix {N p : ℕ} (hp : p ≤ N) (Y : Matrix (Fin N) (Fin p) ℂ) :
    (extend Y).submatrix id (Fin.castLE hp) = Y := by
  ext a j
  simp [extend]

theorem det_extend {N p : ℕ} {hp : p ≤ N} {Y : Matrix (Fin N) (Fin p) ℂ} (h : IsGraph hp Y) : (extend Y).det = 1 := by
  have key : ∀ a b : Fin N, a ≤ b → extend Y a b = (1 : Matrix (Fin N) (Fin N) ℂ) a b := fun a b hab => by
    rw [extend, of_apply]
    split_ifs with hb
    · have ha : (a : ℕ) < p := lt_of_le_of_lt hab hb
      have := congrFun (congrFun h.1 ⟨a, ha⟩) ⟨b, hb⟩
      simpa [one_apply, Fin.ext_iff] using this
    · rfl
  rw [det_of_isLowerTriangular _ fun a b hab => by
    have hab' : a < b := hab
    rw [key a b hab'.le, one_apply_ne hab'.ne]]
  simp [key]

theorem span_col {N p : ℕ} (hp : p ≤ N) (m : Matrix (Fin N) (Fin N) ℂ) :
    Submodule.span ℂ (ReciprocityTheory.ChartRestriction.G.FD.col m '' {a | (a : ℕ) < p}) =
      LinearMap.range (m.submatrix id (Fin.castLE hp)).mulVecLin := by
  rw [range_mulVecLin]
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.castLE hp j, j.2, rfl⟩

theorem submatrix_mul_upper {N p : ℕ} (hp : p ≤ N) (y b : Matrix (Fin N) (Fin N) ℂ)
    (hb : ∀ a c, c < a → b a c = 0) :
    (y * b).submatrix id (Fin.castLE hp) =
      y.submatrix id (Fin.castLE hp) * b.submatrix (Fin.castLE hp) (Fin.castLE hp) := by
  ext a j
  simp only [submatrix_apply, mul_apply, id]
  rw [sum_castLE hp fun k => y a k * b k (Fin.castLE hp j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · rfl
  · rw [hb k _ (by have := j.2; simp only [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]

theorem gramPos_iff {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {N : ℕ} (X : Data E N)
    {x : Frame X.Ψ N} {τ : X.Ψ} {P y : Matrix (Fin N) (Fin N) ℂ} (hP : gram τ.1 X.Gm P = Jm N X.p0)
    (hx : mat x τ = P * y) :
    (X.gramPos x τ).PosDef ↔ ((y.submatrix id (Fin.castLE X.p0_le))ᴴ * Jm N X.p0 *
      y.submatrix id (Fin.castLE X.p0_le)).PosDef := by
  have h1 : (X.gramPos x τ)ᵀ = (y.submatrix id (Fin.castLE X.p0_le))ᴴ * Jm N X.p0 *
      y.submatrix id (Fin.castLE X.p0_le) := by
    have h2 : (gram τ.1 X.Gm (mat x τ))ᵀ = yᴴ * Jm N X.p0 * y := by
      rw [hx, FrameDegreeData.gram_mul, hP, transpose_mul, transpose_mul, transpose_transpose, Jm, diagonal_transpose,
        Matrix.mul_assoc]
      rfl
    rw [Data.gramPos, transpose_submatrix, h2]
    rfl
  rw [← h1]
  exact ⟨fun h => h.transpose, fun h => by simpa using h.transpose⟩

theorem orbit_limit : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ)
    (M : ℕ) (x : ℂ → Frame X.Ψ N), IsOrbit X T M 1 x → ∃ x₀ ∈ X.dom, ∃ x' : ℂ → Frame X.Ψ N,
      Tendsto x' imTop (𝓝 x₀) ∧ ∀ᶠ w in imTop, x' w ∈ X.dom ∧ SamePos X (x w) (x' w) := by
  intro E _ _ _ N X T M x ⟨hM, _, hd, hdom, hper⟩
  choose P hP0 hP using X.signature
  have hp := X.p0_le
  let U : X.Ψ → ℂ → Matrix (Fin N) (Fin X.p0) ℂ := fun τ w => ((P τ)⁻¹ * mat (x w) τ).submatrix id (Fin.castLE hp)
  let Y : X.Ψ → ℂ → Matrix (Fin N) (Fin X.p0) ℂ := fun τ w => U τ w * ((U τ w).submatrix (Fin.castLE hp) id)⁻¹
  have hx : ∀ τ w, mat (x w) τ = P τ * ((P τ)⁻¹ * mat (x w) τ) := fun τ w =>
    (mul_nonsing_inv_cancel_left _ _ (hP0 τ).isUnit).symm
  have hU : ∀ τ (w : ℂ), T < w.im → ((U τ w)ᴴ * Jm N X.p0 * U τ w).PosDef := fun τ w hw =>
    (gramPos_iff X (hP τ) (hx τ w)).1 (X.gramPos_posDef (hdom w hw) τ)
  have hUd : ∀ τ a j, DifferentiableOn ℂ (fun w => U τ w a j) {w | T < w.im} := fun τ a j =>
    DifferentiableOn.fun_sum (u := Finset.univ) fun k _ =>
      (differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hd τ) k) (Fin.castLE hp j)).const_mul
        ((P τ)⁻¹ a k)
  have hG : ∀ τ (w : ℂ), T < w.im → IsGraph hp (Y τ w) := fun τ w hw => isGraph_mul_inv hp (hU τ w hw)
  have hlim : ∀ τ, ∃ Y₀, IsGraph hp Y₀ ∧ ∀ a j, Tendsto (fun w => Y τ w a j) imTop (𝓝 (Y₀ a j)) := fun τ => by
    refine graph_limit hp (T := T) (h := M) (by exact_mod_cast hM) (fun a j => ?_) (fun w hw => ?_) (hG τ)
    · exact DifferentiableOn.fun_sum (u := Finset.univ) fun k _ => (hUd τ a k).fun_mul
        (GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv (fun w => (U τ w).submatrix (Fin.castLE hp) id) _
          (fun i l => hUd τ _ l) (fun w hw => det_top_ne hp (hU τ w hw)) k j)
    · obtain ⟨b, hb, -, hxb⟩ := hper w hw
      have h1 : mat (x (w + M)) τ = mat (x w) τ * mat b τ := by
        rw [hxb]
        show ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * mat b τ = _
        simp
      set c := (mat b τ).submatrix (Fin.castLE hp) (Fin.castLE hp) with hc
      have h2 : U τ (w + M) = U τ w * c := by
        simp only [U]
        rw [h1, ← Matrix.mul_assoc, submatrix_mul_upper hp _ (mat b τ) (hb τ).2]
      have h3 : (U τ w * c).submatrix (Fin.castLE hp) id = (U τ w).submatrix (Fin.castLE hp) id * c := rfl
      have h4 := det_top_ne hp (hU τ (w + M) (by simpa using hw))
      rw [h2, h3, det_mul] at h4
      simp only [Y, Complex.ofReal_natCast]
      rw [h2, h3, Matrix.mul_inv_rev, Matrix.mul_assoc,
        mul_nonsing_inv_cancel_left _ _ (right_ne_zero_of_mul h4).isUnit]
  choose Y₀ hY₀ hlim using hlim
  let fr : (X.Ψ → Matrix (Fin N) (Fin X.p0) ℂ) → Frame X.Ψ N := fun Z τ =>
    (P τ * extend (Z τ) : Matrix (Fin N) (Fin N) ℂ)
  have hfr : ∀ Z τ, mat (fr Z) τ = P τ * extend (Z τ) := fun _ _ => rfl
  have hmem : ∀ Z, (∀ τ, IsGraph hp (Z τ)) → fr Z ∈ X.dom := fun Z hZ =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨by
      rw [hfr, det_mul, det_extend (hZ τ), mul_one]
      exact hP0 τ, (gramPos_iff X (hP τ) (hfr Z τ)).2 (by rw [extend_submatrix]; exact (hZ τ).2)⟩
  refine ⟨fr Y₀, hmem _ hY₀, fun w => fr fun τ => Y τ w, ?_, (eventually_imTop T).mono fun w hw =>
    ⟨hmem _ fun τ => hG τ w hw, fun τ => ?_⟩⟩
  · refine tendsto_pi_nhds.2 fun τ => tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
    refine tendsto_finsetSum Finset.univ (f := fun k w => P τ a k * extend (Y τ w) k b)
      (a := fun k => P τ a k * extend (Y₀ τ) k b) fun k _ => Tendsto.const_mul _ ?_
    simp only [extend, of_apply]
    split_ifs with hb
    · exact hlim τ k _
    · exact tendsto_const_nhds
  · have h1 : (mat (x w) τ).submatrix id (Fin.castLE hp) = P τ * U τ w := by
      conv_lhs => rw [hx τ w]
      rfl
    have h2 : (P τ * extend (Y τ w)).submatrix id (Fin.castLE hp) =
        P τ * U τ w * ((U τ w).submatrix (Fin.castLE hp) id)⁻¹ := by
      rw [Matrix.mul_assoc, ← extend_submatrix hp (U τ w * _)]
      rfl
    rw [span_col hp, span_col hp, hfr, h1, h2, mulVecLin_mul (P τ * U τ w), LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 (mulVec_surjective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ (det_top_ne hp (hU τ w hw)).isUnit)))

end GlobalTheory.ShFam.OrbitLimit
