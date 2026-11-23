import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Lm (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) : ℝ := Real.log ‖dmin X.Gm x τ i‖

theorem dmin_ne_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
  have h1 := (hx τ).2 i
  rw [h] at h1
  simp at h1

theorem phla_eq {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    phla X la x = ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Lm X x τ i.succ - Lm X x τ i.castSucc) := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i => dmin_ne_zero X hx τ i
  have hp : ∀ τ (i : Fin r), 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
    fun τ i => norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))
  unfold phla Data.nfac
  rw [Real.log_prod (fun τ _ => Finset.prod_ne_zero_iff.mpr
    (fun i _ => (Real.rpow_pos_of_pos (hp τ i) _).ne')), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hp τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.log_rpow (hp τ i), norm_div,
    Real.log_div (norm_ne_zero_iff.mpr (hd τ _)) (norm_ne_zero_iff.mpr (hd τ _))]
  simp only [Lm]
  ring

theorem log_densF_eq (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Real.log (densF X x0 z) = ∑ τ, ∑ i : Fin r, (-2) * Lm X (cpt X x0 z) τ i.castSucc := by
  have hx : cpt X x0 z ∈ X.dom := hz
  have hd : ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := fun τ i => dmin_ne_zero X hx τ i
  unfold densF
  rw [Real.log_prod (fun τ _ => Finset.prod_ne_zero_iff.mpr
    (fun i _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hd τ _))))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Real.log_prod (fun i _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hd τ _)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.log_zpow]
  simp only [Lm]
  push_cast
  try ring

private theorem sum_range_two_mul_sub_mul_sub_eq (L : ℕ → ℝ) (c : ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range r, ((2 * i : ℝ) - c) * (L (i + 1) - L i) =
      2 * r * L r - 2 * ∑ i ∈ Finset.range r, L (i + 1) - c * L r + c * L 0 := by
  induction r with
  | zero => simp only [Finset.sum_range_zero, Nat.cast_zero]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

theorem sbp (L : ℕ → ℝ) : ∀ r : ℕ, ∑ i ∈ Finset.range r, ((2 * i : ℝ) - ((r : ℝ) - 1)) * (L (i + 1) - L i) =
    ((r : ℝ) - 1) * L r - 2 * ∑ i ∈ Finset.range r, L i + ((r : ℝ) + 1) * L 0
  | 0 => by simp
  | r + 1 => by
    have ih := sbp L r
    have htel : ∑ i ∈ Finset.range r, (L (i + 1) - L i) = L r - L 0 := Finset.sum_range_sub L r
    have hsplit : ∑ i ∈ Finset.range r, ((2 * i : ℝ) - (((r + 1 : ℕ) : ℝ) - 1)) * (L (i + 1) - L i) =
        ∑ i ∈ Finset.range r, ((2 * i : ℝ) - ((r : ℝ) - 1)) * (L (i + 1) - L i) -
          ∑ i ∈ Finset.range r, (L (i + 1) - L i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [Finset.sum_range_succ, hsplit, ih, htel, Finset.sum_range_succ]
    push_cast
    ring

theorem Lm_zero (x : Frame X.Ψ r) (τ : X.Ψ) : Lm X x τ 0 = 0 := by
  unfold Lm dmin lminor
  haveI : IsEmpty (Fin ((0 : Fin (r + 1)) : ℕ)) := ⟨fun i => by have := i.isLt; simp at this⟩
  rw [Matrix.det_isEmpty]
  simp

private theorem gram_eq_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem Lm_last_cpt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    Lm X (cpt X x0 z) τ (Fin.last r) = 0 := by
  have hN : (mat (nmat X z) τ).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [mat, nmat]
    · intro a b hab
      have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
      simp [mat, nmat, not_lt.mpr hab'.le, hab'.ne]
  have hNc : ((mat (nmat X z) τ).map (starRingEnd ℂ)).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hN, map_one]
  have key : dmin X.Gm (cpt X x0 z) τ (Fin.last r) = (gram τ.1 X.Gm (mat (cpt X x0 z) τ)).det := rfl
  have e1 : mat (cpt X x0 z) τ = mat x0 τ * mat (nmat X z) τ := rfl
  have hs : ∀ a : Fin r, ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ)‖ = 1 := fun a => by
    unfold sgn; split_ifs <;> simp
  rw [Lm, key, e1, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul,
    show ∀ A B C D F : Matrix (Fin r) (Fin r) ℂ, A * B * C * (D * F) = A * (B * C * D) * F from
      fun A B C D F => by simp only [Matrix.mul_assoc],
    ← gram_eq_lemma τ.1 X.Gm (mat x0 τ), ho τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hN, hNc, Matrix.det_diagonal]
  simp only [one_mul, mul_one, norm_prod, hs, Finset.prod_const_one, Real.log_one]

theorem phla_kapW_cpt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    phla X (kapW X) (cpt X x0 z) = Real.log (densF X x0 z) := by
  have hx : cpt X x0 z ∈ X.dom := hz
  rw [phla_eq X hx, log_densF_eq X x0 hz]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  obtain ⟨L, hL⟩ : ∃ L : ℕ → ℝ,
      L = fun n => if h : n < r + 1 then Lm X (cpt X x0 z) τ ⟨n, h⟩ else 0 := ⟨_, rfl⟩
  have h1 : ∀ i : Fin r, Lm X (cpt X x0 z) τ i.succ = L ((i : ℕ) + 1) := fun i => by
    rw [hL]
    dsimp only
    rw [dif_pos (show (i : ℕ) + 1 < r + 1 by have := i.isLt; omega)]
    try rfl
  have h2 : ∀ i : Fin r, Lm X (cpt X x0 z) τ i.castSucc = L (i : ℕ) := fun i => by
    rw [hL]
    dsimp only
    rw [dif_pos (show (i : ℕ) < r + 1 by have := i.isLt; omega)]
    try rfl
  have hk : ∀ i : Fin r, ((kapW X τ i : ℤ) : ℝ) = (2 * (i : ℕ) : ℝ) - ((r : ℝ) - 1) := fun i => by
    simp only [kapW]
    push_cast
    try ring
  have hr : L r = 0 := by
    rw [hL]
    dsimp only
    rw [dif_pos (show r < r + 1 by omega)]
    exact Lm_last_cpt X x0 ho z τ
  have e0 : (⟨0, Nat.succ_pos r⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
  have h0 : L 0 = 0 := by
    rw [hL]
    dsimp only
    rw [dif_pos (show 0 < r + 1 by omega), e0]
    exact Lm_zero X _ τ
  simp only [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((2 * i : ℝ) - ((r : ℝ) - 1)) * (L (i + 1) - L i)) r,
    Fin.sum_univ_eq_sum_range (fun i => (-2) * L i) r, sbp L r, hr, h0, ← Finset.mul_sum]
  ring

theorem cpt_entry_cd (x0 : Frame X.Ψ r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => cpt X x0 z τ a b := by
  have hN : ∀ k : Fin r, ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ k b := by
    intro k
    by_cases h : b < k
    · simp only [nmat, dif_pos h]
      exact (show V (nd X) →L[ℂ] ℂ from EuclideanSpace.proj _).contDiff
    · simp only [nmat, dif_neg h]
      exact contDiff_const
  show ContDiff ℂ ∞ fun z : V (nd X) => (mat x0 τ * mat (nmat X z) τ) a b
  simp only [Matrix.mul_apply, mat, Matrix.of_apply]
  exact ContDiff.sum (fun k _ => contDiff_const.mul (hN k))

theorem gram_cpt_cd (x0 : Frame X.Ψ r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun z : V (nd X) => FD.gram τ.1 X.Gm (mat (cpt X x0 z) τ) a b := by
  have hc : ∀ a b : Fin r, ContDiff ℝ ∞ fun z : V (nd X) => cpt X x0 z τ a b :=
    fun a b => (cpt_entry_cd X x0 τ a b).restrict_scalars ℝ
  have hcj : ∀ a b : Fin r, ContDiff ℝ ∞ fun z : V (nd X) => (starRingEnd ℂ) (cpt X x0 z τ a b) := by
    intro a b
    first
    | exact Complex.conjCLE.contDiff.comp (hc a b)
    | simpa [Function.comp_def] using Complex.conjCLE.contDiff.comp (hc a b)
  simp only [gram, hermC, col, Matrix.of_apply, mat]
  refine ContDiff.sum (fun k _ => ContDiff.sum (fun l _ => ?_))
  exact ((hc k a).mul contDiff_const).mul (hcj l b)

theorem dmin_cpt_cd (x0 : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    ContDiff ℝ ∞ fun z : V (nd X) => dmin X.Gm (cpt X x0 z) τ i := by
  unfold dmin lminor
  simp only [Matrix.det_apply', Matrix.submatrix_apply]
  refine ContDiff.sum (fun σ _ => contDiff_const.mul ?_)
  first
  | exact contDiff_prod (fun j _ => gram_cpt_cd X x0 τ _ _)
  | fun_prop

theorem log_norm_eq (w : ℂ) : Real.log ‖w‖ = Real.log (Complex.normSq w) / 2 := by
  rw [Complex.normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring

theorem Lm_cpt_cdAt (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) (τ : X.Ψ) (i : Fin (r + 1)) :
    ContDiffAt ℝ ∞ (fun w => Lm X (cpt X x0 w) τ i) z := by
  have hd : dmin X.Gm (cpt X x0 z) τ i ≠ 0 := dmin_ne_zero X hz τ i
  have hf := dmin_cpt_cd X x0 τ i
  have hre : ContDiff ℝ ∞ fun w => (dmin X.Gm (cpt X x0 w) τ i).re := Complex.reCLM.contDiff.comp hf
  have him : ContDiff ℝ ∞ fun w => (dmin X.Gm (cpt X x0 w) τ i).im := Complex.imCLM.contDiff.comp hf
  simp only [Lm, log_norm_eq, Complex.normSq_apply]
  refine ContDiffAt.div_const ?_ 2
  refine ((hre.mul hre).add (him.mul him)).contDiffAt.log ?_
  rw [← Complex.normSq_apply]
  exact (Complex.normSq_pos.mpr hd).ne'

private theorem contDiff_det_mat_cpt (x0 : Frame X.Ψ r) (τ : X.Ψ) :
    ContDiff ℂ ∞ fun w : V (nd X) => (mat (cpt X x0 w) τ).det := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  refine ContDiff.sum (fun σ _ => contDiff_const.mul ?_)
  first
  | exact contDiff_prod (fun j _ => cpt_entry_cd X x0 τ _ _)
  | fun_prop

private theorem eventually_mem_omF (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ∀ᶠ w in 𝓝 z, w ∈ OmF X x0 := by
  have hz' : cpt X x0 z ∈ X.dom := hz
  show ∀ᶠ w in 𝓝 z, cpt X x0 w ∈ X.dom
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hz' ⊢
  rw [Filter.eventually_all]
  intro τ
  refine Filter.Eventually.and ?_ ?_
  · have hc : Continuous fun w : V (nd X) => (mat (cpt X x0 w) τ).det :=
      (contDiff_det_mat_cpt X x0 τ).continuous
    exact hc.continuousAt.eventually_ne (hz' τ).1
  · rw [Filter.eventually_all]
    intro i
    have hc : Continuous fun w : V (nd X) => psgn X.p0 i * (dmin X.Gm (cpt X x0 w) τ i).re :=
      continuous_const.mul (Complex.continuous_re.comp (dmin_cpt_cd X x0 τ i).continuous)
    exact hc.continuousAt.eventually (Ioi_mem_nhds ((hz' τ).2 i))

theorem phla_cpt_eventually (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) (la : Wt X.Ψ r) :
    (fun w => phla X la (cpt X x0 w)) =ᶠ[𝓝 z]
      fun w => ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Lm X (cpt X x0 w) τ i.succ - Lm X (cpt X x0 w) τ i.castSucc) := by
  filter_upwards [eventually_mem_omF X x0 hz] with w hw
  exact phla_eq X hw la

theorem phla_cpt_cdAt (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) (la : Wt X.Ψ r) :
    ContDiffAt ℝ ∞ (fun w => phla X la (cpt X x0 w)) z := by
  refine ContDiffAt.congr_of_eventuallyEq ?_ (phla_cpt_eventually X x0 hz la)
  refine ContDiffAt.sum (fun τ _ => ContDiffAt.sum (fun i _ => ?_))
  exact contDiffAt_const.mul ((Lm_cpt_cdAt X x0 hz τ _).sub (Lm_cpt_cdAt X x0 hz τ _))

theorem logDens_cdAt (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun w => Real.log (densF X x0 w)) z := by
  refine ContDiffAt.congr_of_eventuallyEq ?_
    ((eventually_mem_omF X x0 hz).mono (fun w hw => log_densF_eq X x0 hw))
  exact ContDiffAt.sum (fun τ _ => ContDiffAt.sum (fun i _ =>
    contDiffAt_const.mul (Lm_cpt_cdAt X x0 hz τ _)))

omit [NumberField E] [IsCMField E] in
@[simp] theorem V_zero_app {m : ℕ} (i : Fin m) : (0 : V m) i = 0 := rfl

theorem nmat_zero (τ : X.Ψ) : mat (nmat X (0 : V (nd X))) τ = 1 := by
  ext a b
  by_cases h : b < a
  · simp [mat, nmat, Matrix.one_apply, h, h.ne']
    first
    | exact V_zero_app _
    | rfl
  · simp [mat, nmat, Matrix.one_apply, h]

theorem cpt_zero (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  show mat x0 τ * mat (nmat X 0) τ = x0 τ
  rw [nmat_zero, Matrix.mul_one]
  try rfl

private theorem mem_dom_of_isOrth' (x0 : Frame X.Ψ r) (ho : IsOrth X x0) : x0 ∈ X.dom := by
  have hsq : ∀ a : ℕ, sgn X.p0 a * sgn X.p0 a = 1 := fun a => by
    unfold sgn; split_ifs <;> norm_num
  have hd : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), dmin X.Gm x0 τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    intro τ i
    unfold dmin lminor
    rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]
    rfl
  simp only [Data.dom, GG, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · intro h0
    have h3 := congrArg Matrix.det (ho τ)
    rw [gram_eq_lemma, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
      Matrix.det_diagonal] at h3
    exact (Finset.prod_ne_zero_iff.mpr (fun a _ => Complex.ofReal_ne_zero.mpr
      (by unfold sgn; split_ifs <;> norm_num))) h3.symm
  · have hps : psgn X.p0 i * psgn X.p0 i = 1 := by
      unfold psgn
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun a _ => hsq a)
    rw [hd τ i, Complex.ofReal_re, hps]
    exact one_pos

theorem zero_mem_OmF (x0 : Frame X.Ψ r) (ho : IsOrth X x0) : (0 : V (nd X)) ∈ OmF X x0 := by
  show cpt X x0 0 ∈ X.dom
  rw [cpt_zero]
  exact mem_dom_of_isOrth' X x0 ho

theorem orth_mem_dom (x0 : Frame X.Ψ r) (ho : IsOrth X x0) : x0 ∈ X.dom := by
  exact mem_dom_of_isOrth' X x0 ho

theorem phla_comb {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la1 la2 : Wt X.Ψ r) (k : ℕ) :
    phla X (la1 - kapW X - k • la2) x = phla X la1 x - phla X (kapW X) x - k * phla X la2 x := by
  simp only [phla_eq X hx]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e : (((la1 - kapW X - k • la2) τ i : ℤ) : ℝ) =
      (la1 τ i : ℝ) - (kapW X τ i : ℝ) - (k : ℝ) * (la2 τ i : ℝ) := by
    simp
  rw [e]
  ring

private theorem leviV_sub_sub_const_mul_of_eventuallyEq {n : ℕ} (f f1 f2 f3 : V n → ℂ) (c : ℂ) (z : V n) (ξ : Fin n → ℂ)
    (hev : f =ᶠ[𝓝 z] fun w => f1 w - f2 w - c * f3 w)
    (h1 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ f1 w) (h2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ f2 w)
    (h3 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ f3 w) :
    leviV n f z ξ = leviV n f1 z ξ - leviV n f2 z ξ - c * leviV n f3 z ξ := by
  have hle1 : (1 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact mod_cast le_top
    | simp
  have hle2 : (1 : WithTop ℕ∞) + 1 ≤ ∞ := by
    rw [one_add_one_eq_two]
    first
    | exact WithTop.coe_le_coe.mpr le_top
    | exact (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
    | exact mod_cast le_top
    | simp
    | decide
  have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := (lt_of_lt_of_le zero_lt_one hle1).ne'
  have hD : ∀ᶠ w in 𝓝 z, fderiv ℝ f w = fderiv ℝ f1 w - fderiv ℝ f2 w - c • fderiv ℝ f3 w := by
    filter_upwards [hev.eventuallyEq_nhds, h1, h2, h3] with w hw hw1 hw2 hw3
    rw [hw.fderiv_eq]
    exact (((hw1.differentiableAt hn0).hasFDerivAt.sub (hw2.differentiableAt hn0).hasFDerivAt).sub
      ((hw3.differentiableAt hn0).hasFDerivAt.const_mul c)).fderiv
  have hW : ∀ l, wdb n l f =ᶠ[𝓝 z] fun w => wdb n l f1 w - wdb n l f2 w - c * wdb n l f3 w := by
    intro l
    filter_upwards [hD] with w hw
    simp only [wdb, hw, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hWd : ∀ g : V n → ℂ, (∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ g w) → ∀ l,
      DifferentiableAt ℝ (wdb n l g) z := by
    intro g hg l
    have hf' : DifferentiableAt ℝ (fderiv ℝ g) z :=
      ((hg.self_of_nhds).fderiv_right hle2).differentiableAt one_ne_zero
    have hv : ∀ v : V n, DifferentiableAt ℝ (fun y => fderiv ℝ g y v) z :=
      fun v => hf'.clm_apply (differentiableAt_const v)
    have hsum : DifferentiableAt ℝ (fun y => fderiv ℝ g y (bas n l) +
        Complex.I * fderiv ℝ g y (Complex.I • bas n l)) z :=
      (hv _).add ((hv _).const_mul Complex.I)
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas n l) +
      Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2) z
    simp only [div_eq_mul_inv]
    exact hsum.mul_const _
  have hwd : ∀ j l, wd n j (wdb n l f) z =
      wd n j (wdb n l f1) z - wd n j (wdb n l f2) z - c * wd n j (wdb n l f3) z := by
    intro j l
    have d1 := hWd f1 h1 l
    have d2 := hWd f2 h2 l
    have d3 := hWd f3 h3 l
    have e2 : fderiv ℝ (fun w => wdb n l f1 w - wdb n l f2 w - c * wdb n l f3 w) z =
        fderiv ℝ (wdb n l f1) z - fderiv ℝ (wdb n l f2) z - c • fderiv ℝ (wdb n l f3) z :=
      ((d1.hasFDerivAt.sub d2.hasFDerivAt).sub (d3.hasFDerivAt.const_mul c)).fderiv
    unfold wd
    rw [(hW l).fderiv_eq, e2]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  unfold leviV
  simp only [hwd]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem leviM_comb (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (la1 la2 : Wt X.Ψ r) (k : ℕ) (ξ : Fin (nd X) → ℂ) :
    leviM X (phla X (la1 - kapW X - k • la2)) x0 z ξ =
      leviO X x0 (phla X la1) z ξ - leviDens X x0 z ξ - k * leviO X x0 (phla X la2) z ξ := by
  unfold leviO leviDens leviM
  have hev := eventually_mem_omF X x0 hz
  rw [leviV_sub_sub_const_mul_of_eventuallyEq (fun w => ((phla X (la1 - kapW X - k • la2) (cpt X x0 w) : ℝ) : ℂ))
      (fun w => ((phla X la1 (cpt X x0 w) : ℝ) : ℂ)) (fun w => ((Real.log (densF X x0 w) : ℝ) : ℂ))
      (fun w => ((phla X la2 (cpt X x0 w) : ℝ) : ℂ)) (k : ℂ) z ξ ?_ ?_ ?_ ?_]
  · first
    | (simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
        sub_zero]; done)
    | simp
  · filter_upwards [hev] with w hw
    have hw' : cpt X x0 w ∈ X.dom := hw
    try dsimp only
    rw [phla_comb X hw' la1 la2 k, phla_kapW_cpt X x0 ho hw]
    push_cast
    try ring
  · filter_upwards [hev] with w hw
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp w (phla_cpt_cdAt X x0 hw la1)
  · filter_upwards [hev] with w hw
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp w (logDens_cdAt X x0 hw)
  · filter_upwards [hev] with w hw
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp w (phla_cpt_cdAt X x0 hw la2)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
