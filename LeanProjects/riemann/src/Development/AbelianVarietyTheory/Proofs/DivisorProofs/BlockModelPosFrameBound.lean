import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricBoundPuncturedPolydiscStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricGramMatrixLocalHolomorphicImPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionMatrixGramOperatorNormLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulInvMulPosSemidefUniformBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurComplementBlockQuadraticLowerBound
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

open Matrix Filter Topology GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.CurvInterp.Block

section Norms

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem le_of_sq_le_mul {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ^ 2 ≤ c * x) : x ≤ c := by
  rcases hx.eq_or_lt with h0 | h0
  · rwa [← h0]
  · nlinarith

theorem opNorm_neg_transpose_le {H : Matrix n n ℂ} (hH : H.PosDef) (T : Matrix n n ℂ) :
    opNorm (dualGram H) (dualGram H) (-Tᵀ) ≤ opNorm H H T := by
  have hu : IsUnit H.det := (isUnit_iff_isUnit_det _).1 hH.isUnit
  have hD : (dualGram H).PosDef := hH.inv.transpose
  have h1 : ∀ v u : n → ℂ, form H v (star (H⁻¹ *ᵥ u)) = v ⬝ᵥ u := fun v u => by
    rw [form, star_star, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have h2 : ∀ u : n → ℂ, gnorm H (star (H⁻¹ *ᵥ u)) = gnorm (dualGram H) u := fun u => by
    rw [gnorm, gnorm, h1, form_eq_transpose, dualGram, transpose_transpose, ← Complex.conj_re, ← RCLike.star_def,
      star_dotProduct, star_star, dotProduct_comm]
  refine opNorm_le_of_bound (opNorm_nonneg _ _ _) fun u => ?_
  have e : (-Tᵀ) *ᵥ u = (-1 : ℂ) • (Tᵀ *ᵥ u) := by rw [neg_mulVec]; simp
  rw [e, gnorm_smul hD.posSemidef, norm_neg, norm_one, one_mul]
  refine le_of_sq_le_mul (gnorm_nonneg _ _) (mul_nonneg (opNorm_nonneg _ _ _) (gnorm_nonneg _ _)) ?_
  set w := star (H⁻¹ *ᵥ (Tᵀ *ᵥ u)) with hw
  have e2 : form H w w = form H (T *ᵥ w) (star (H⁻¹ *ᵥ u)) :=
    (h1 w (Tᵀ *ᵥ u)).trans (by rw [h1, dotProduct_mulVec, vecMul_transpose])
  rw [← h2 (Tᵀ *ᵥ u), ← hw, gnorm_sq hH.posSemidef, e2]
  refine (Complex.re_le_norm _).trans ((norm_form_le hH.posSemidef _ _).trans ?_)
  rw [h2, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (gnorm_mulVec_le hH hH.posSemidef T w) (gnorm_nonneg _ _)

theorem opNorm_conj_le {K A : Matrix n n ℂ} (hK : K.PosDef) (hA : IsUnit A.det) (F : Matrix n n ℂ) :
    opNorm (Aᵀ * K * Aᴴᵀ) (Aᵀ * K * Aᴴᵀ) (A⁻¹ * F * A) ≤ opNorm K K F := by
  have h : ∀ v, gnorm (Aᵀ * K * Aᴴᵀ) v = gnorm K (A *ᵥ v) := fun v => by
    rw [gnorm, gnorm, form_mulVec, form]
  refine opNorm_le_of_bound (opNorm_nonneg _ _ _) fun v => ?_
  rw [h, h, mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hA, ← mulVec_mulVec]
  exact gnorm_mulVec_le hK hK.posSemidef F _

theorem opNorm_submatrix_le {M : Matrix n n ℂ} (hM : M.PosDef) {j : m → n} (hj : Function.Injective j)
    (h0 : ∀ s b, s ∉ Set.range j → M s (j b) = 0) (T : Matrix n n ℂ) :
    opNorm (M.submatrix j j) (M.submatrix j j) (T.submatrix j j) ≤ opNorm M M T := by
  set J : Matrix n m ℂ := (1 : Matrix n n ℂ).submatrix id j with hJ
  have hN : (M.submatrix j j).PosDef := hM.submatrix hj
  have hMJ : M * J = J * M.submatrix j j := by
    ext s b
    by_cases hs : s ∈ Set.range j
    · obtain ⟨a, rfl⟩ := hs
      simp [hJ, mul_apply, one_apply, hj.eq_iff]
    · have : ∀ a, s ≠ j a := fun a h => hs ⟨a, h.symm⟩
      simp [hJ, mul_apply, one_apply, this, h0 s b hs]
  have hstar : ∀ u, star (J *ᵥ u) = J *ᵥ star u := fun u => by
    ext s; simp [hJ, mulVec, dotProduct, one_apply, apply_ite]
  have hJJ : Jᵀ * J = 1 := by
    ext a b; simp [hJ, mul_apply, one_apply, hj.eq_iff]
  have hT : T.submatrix j j = Jᵀ * T * J := by
    ext a b; simp [hJ, mul_apply, one_apply]
  have h1 : ∀ w u, form M w (J *ᵥ u) = form (M.submatrix j j) (Jᵀ *ᵥ w) u := fun w u => by
    rw [form, form, hstar, mulVec_mulVec, hMJ, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
  have h2 : ∀ u, gnorm M (J *ᵥ u) = gnorm (M.submatrix j j) u := fun u => by
    rw [gnorm, gnorm, h1, mulVec_mulVec, hJJ, one_mulVec]
  refine opNorm_le_of_bound (opNorm_nonneg _ _ _) fun v => ?_
  refine le_of_sq_le_mul (gnorm_nonneg _ _) (mul_nonneg (opNorm_nonneg _ _ _) (gnorm_nonneg _ _)) ?_
  rw [gnorm_sq hN.posSemidef]
  conv_lhs => enter [1, 2]; rw [hT, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [← h1]
  refine (Complex.re_le_norm _).trans ((norm_form_le hM.posSemidef _ _).trans ?_)
  rw [h2, ← h2 v]
  exact mul_le_mul_of_nonneg_right (gnorm_mulVec_le hM hM.posSemidef T _) (gnorm_nonneg _ _)

theorem opNorm_smul_metric_le {H : Matrix n n ℂ} (hH : H.PosDef) {c : ℝ} (hc : 0 ≤ c) (T : Matrix n n ℂ) :
    opNorm ((c : ℂ) • H) ((c : ℂ) • H) T ≤ opNorm H H T := by
  have h : ∀ v, gnorm ((c : ℂ) • H) v = √c * gnorm H v := fun v => by
    rw [gnorm, gnorm, form_smul, Complex.re_ofReal_mul, Real.sqrt_mul hc]
  refine opNorm_le_of_bound (opNorm_nonneg _ _ _) fun v => ?_
  rw [h, h, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (gnorm_mulVec_le hH hH.posSemidef T v) (Real.sqrt_nonneg _)

end Norms

section Frames

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem conn_submatrix {M : E → Matrix n n ℂ} {z : E} (hM : (M z).PosDef) {j : m → n} (hj : Function.Injective j)
    (h0 : ∀ s b, s ∉ Set.range j → M z s (j b) = 0) (ξ : E) :
    conn (fun x => (M x).submatrix j j) z ξ = (conn M z ξ).submatrix j j := by
  refine (eq_conn_of_compatible (H := fun x => (M x).submatrix j j) (z := z)
    ((isUnit_iff_isUnit_det _).1 (hM.submatrix hj).isUnit) ?_).symm
  ext a b
  have h := congrFun (congrFun (conn_transpose_mul ((isUnit_iff_isUnit_det _).1 hM.isUnit) ξ) (j a)) (j b)
  refine Eq.trans ?_ h
  simp only [mul_apply, transpose_apply, submatrix_apply]
  refine Finset.sum_of_injOn j hj.injOn (fun _ _ => Finset.mem_univ _) (fun s _ hs => ?_) fun _ _ => rfl
  rw [h0 s b (by simpa using hs), mul_zero]

theorem curv_submatrix {M : E → Matrix n n ℂ} {z : E} {j : m → n} (hj : Function.Injective j)
    (h : ∀ᶠ x in 𝓝 z, (M x).PosDef ∧ ∀ s b, s ∉ Set.range j → M x s (j b) = 0) (ξ η : E) :
    curv (fun x => (M x).submatrix j j) z ξ η = (curv M z ξ η).submatrix j j := by
  rw [curv, mdbar_congr (B := fun x => (conn M x ξ).submatrix j j)
    (h.mono fun x hx => conn_submatrix hx.1 hj hx.2 ξ)]
  rfl

theorem conn_const_smul {M : E → Matrix n n ℂ} {z : E} {c : ℝ} (hc : c ≠ 0) (h : MContDiffAt 1 M z)
    (hu : IsUnit (M z).det) (ξ : E) : conn (fun x => (c : ℂ) • M x) z ξ = conn M z ξ := by
  rw [conn_smul (f := fun _ => c) (differentiableAt_const _) hc h hu]; simp

theorem curv_const_smul {M : E → Matrix n n ℂ} {z : E} {c : ℝ} (hc : c ≠ 0) (h : MContDiffAt 2 M z)
    (hu : IsUnit (M z).det) (ξ η : E) : curv (fun x => (c : ℂ) • M x) z ξ η = curv M z ξ η := by
  rw [curv, curv, mdbar_congr (B := fun x => conn M x ξ)]
  filter_upwards [h.eventually_two, h.eventually_isUnit hu] with x h1 h2
  exact conn_const_smul hc (h1.of_le one_le_two) h2 ξ

end Frames

theorem holo_local_bounds {e g : ℕ} {A : (Fin e → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    (hA : ∀ i k, AnalyticAt ℂ (fun z => A z i k) 0) (h0 : IsUnit (A 0).det) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ z in 𝓝 (0 : Fin e → ℂ), IsUnit (A z).det ∧ opNorm 1 1 (A z) ≤ B ∧ opNorm 1 1 (A z)⁻¹ ≤ B ∧
      ∀ ξ, opNorm 1 1 (mdel A z ξ) ≤ B * ‖ξ‖ := by
  have h1 : MContDiffAt 1 A 0 := fun i k => (hA i k).contDiffAt.restrict_scalars ℝ
  let f : (Fin e → ℂ) → (Fin g → Fin g → ℂ × ℂ × ((Fin e → ℂ) →L[ℂ] ℂ)) := fun z i k =>
    (A z i k, (A z)⁻¹ i k, fderiv ℂ (fun x => A x i k) z)
  have hf : ContinuousAt f 0 := continuousAt_pi.2 fun i => continuousAt_pi.2 fun k =>
    (h1 i k).continuousAt.prodMk ((h1.inv h0 i k).continuousAt.prodMk (hA i k).fderiv.continuousAt)
  have hB : 0 ≤ ‖f 0‖ + 1 := by positivity
  refine ⟨g * (‖f 0‖ + 1), by positivity, ?_⟩
  filter_upwards [hf.norm.eventually_lt continuousAt_const (lt_add_one ‖f 0‖), h1.eventually_isUnit h0,
    eventually_all.2 fun i => eventually_all.2 fun k => (hA i k).eventually_analyticAt] with z hz hu ha
  have hik : ∀ i k, ‖f z i k‖ ≤ ‖f 0‖ + 1 := fun i k =>
    (norm_le_pi_norm (f z i) k).trans ((norm_le_pi_norm (f z) i).trans hz.le)
  refine ⟨hu, GlobalTheory.ConnPointwise.opNorm_one_le_of_entry _ hB fun i k => (norm_fst_le (f z i k)).trans (hik i k),
    GlobalTheory.ConnPointwise.opNorm_one_le_of_entry _ hB fun i k => (norm_fst_le (f z i k).2).trans ((norm_snd_le (f z i k)).trans (hik i k)), fun ξ => ?_⟩
  rw [mul_assoc]
  refine GlobalTheory.ConnPointwise.opNorm_one_le_of_entry _ (by positivity) fun i k => ?_
  rw [mdel_apply, GlobalTheory.del_eq_fderiv (ha i k).differentiableAt]
  exact (fderiv ℂ (fun x => A x i k) z).le_of_opNorm_le
    ((norm_snd_le (f z i k).2).trans ((norm_snd_le (f z i k)).trans (hik i k))) ξ

theorem norm_le_gnorm_modelGram {e m : ℕ} (σ : Fin m → Option (Fin e)) {z : Fin e → ℂ} (hz : z ∈ punct σ 1)
    (ξ : Fin e → ℂ) : ‖ξ‖ ≤ gnorm (modelGram σ z) ξ := by
  classical
  refine (pi_norm_le_iff_of_nonneg (gnorm_nonneg _ _)).2 fun k => Real.le_sqrt_of_sq_le ?_
  rw [form_modelGram, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt]
  refine le_trans ?_ (Finset.single_le_sum (fun l _ => ?_) (Finset.mem_univ k))
  · split_ifs with h
    · obtain ⟨i, hi⟩ := h
      have h0 : 0 < ‖z k‖ := norm_pos_iff.2 (hz.2 i k hi)
      have h1 : ‖z k‖ < 1 := (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.1 hz.1)
      have ht : 0 < GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf (z k) := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos (hz.2 i k hi) h1
      have h2 := (abs_lt.1 (Real.abs_log_mul_self_lt _ h0 h1.le)).1
      have h3 : ‖z k‖ * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf (z k) ≤ 1 := by
        rw [GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf, ← mul_div_assoc, div_le_one (by positivity)]
        nlinarith [Real.pi_gt_three]
      rw [le_div_iff₀ (by positivity), ← mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (by positivity) h3)
    · exact le_rfl
  · split_ifs <;> positivity

section Bounds

variable {e g q : ℕ} {V : Set (Fin e → ℂ)} {G : (Fin e → ℂ) → Matrix (Fin e) (Fin e) ℂ}

theorem bounds_dual_changeFrame {Y A : (Fin e → ℂ) → Matrix (Fin g) (Fin g) ℂ} {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hY : IsPosFrame V Y) (h1 : OneFormBound V (fun _ => 1) G (conn Y) C) (h2 : TwoFormBound V Y G (curv Y) C)
    (hA : ∀ z ∈ V, ∀ i k, AnalyticAt ℂ (fun x => A x i k) z)
    (hb : ∀ z ∈ V, IsUnit (A z).det ∧ opNorm 1 1 (A z) ≤ B ∧ opNorm 1 1 (A z)⁻¹ ≤ B ∧
      ∀ ξ, opNorm 1 1 (mdel A z ξ) ≤ B * gnorm (G z) ξ) :
    IsPosFrame V (fun x => (A x)ᵀ * dualGram (Y x) * (A x)ᴴᵀ) ∧
      OneFormBound V (fun _ => 1) G (conn fun x => (A x)ᵀ * dualGram (Y x) * (A x)ᴴᵀ) (B * (C * B + B)) ∧
      TwoFormBound V (fun x => (A x)ᵀ * dualGram (Y x) * (A x)ᴴᵀ) G
        (curv fun x => (A x)ᵀ * dualGram (Y x) * (A x)ᴴᵀ) C := by
  have hY' := hY.isHermFrame
  have hD := hY'.dual
  have hDp : ∀ z ∈ V, (dualGram (Y z)).PosDef := fun z hz => (hY.posDef z hz).inv.transpose
  have hAs : ∀ z ∈ V, ∀ k, MContDiffAt k A z := fun z hz k i l => (hA z hz i l).contDiffAt.restrict_scalars ℝ
  have hA0 : ∀ z ∈ V, ∀ η, mdbar A z η = 0 := fun z hz η => by
    ext i k; simp [GlobalTheory.dbar_eq_zero (hA z hz i k).differentiableAt]
  have hp : ∀ z ∈ V, ((A z)ᵀ * dualGram (Y z) * (A z)ᴴᵀ).PosDef := fun z hz => by
    refine (hDp z hz).mul_mul_conjTranspose_same (B := (A z)ᵀ) ?_
    exact vecMul_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (by rw [det_transpose]; exact (hb z hz).1))
  have one : (1 : Matrix (Fin g) (Fin g) ℂ).PosDef := PosDef.one
  refine ⟨⟨hY.isOpen, fun a b z hz => ((((hAs z hz _).transpose.mul (hD.mContDiffAt hz)).mul
    (hAs z hz _).conjTranspose.transpose) a b).contDiffWithinAt, hp⟩,
    fun z hz => ⟨one, (h1 z hz).2.1, fun ξ => ?_⟩, fun z hz => ⟨hp z hz, (h1 z hz).2.1, fun ξ η => ?_⟩⟩
  · rw [conn_changeFrame (hD.one hz) (hD.isUnit z hz) (hAs z hz _) (hb z hz).1 (hA0 z hz),
      conn_dual (hY'.one hz) (hY'.isUnit z hz)]
    obtain ⟨-, b1, b2, b3⟩ := hb z hz
    have h3 := opNorm_neg_transpose_le one (conn Y z ξ)
    rw [show dualGram (1 : Matrix (Fin g) (Fin g) ℂ) = 1 by simp [dualGram]] at h3
    have h4 := h3.trans ((h1 z hz).2.2 ξ)
    have h5 := gnorm_nonneg (G z) ξ
    have h6 := (opNorm_mul_le one one one.posSemidef _ _).trans (mul_le_mul h4 b1 (opNorm_nonneg _ _ _) (by positivity))
    have h7 := (opNorm_add_le one one.posSemidef _ _).trans (add_le_add h6 (b3 ξ))
    exact (opNorm_mul_le one one one.posSemidef _ _).trans
      ((mul_le_mul b2 h7 (opNorm_nonneg _ _ _) hB).trans_eq (by ring))
  · rw [curv_changeFrame (hD.two hz) (hD.isUnit z hz) (hAs z hz _) (hb z hz).1
      (mem_of_superset (hY.isOpen.mem_nhds hz) hA0), curv_dual (hY'.two hz) (hY'.isUnit z hz)]
    exact (opNorm_conj_le (hDp z hz) (hb z hz).1 _).trans
      ((opNorm_neg_transpose_le (hY.posDef z hz) _).trans ((h2 z hz).2.2 ξ η))

theorem bounds_block {M : (Fin e → ℂ) → Matrix (Fin g) (Fin g) ℂ} {H : (Fin e → ℂ) → Matrix (Fin q) (Fin q) ℂ}
    {C c : ℝ} (hc : 0 < c) {j : Fin q → Fin g} (hj : Function.Injective j) (hM : IsPosFrame V M)
    (h1 : OneFormBound V (fun _ => 1) G (conn M) C) (h2 : TwoFormBound V M G (curv M) C)
    (h0 : ∀ z ∈ V, ∀ s b, s ∉ Set.range j → M z s (j b) = 0)
    (hH : ∀ z ∈ V, H z = (c : ℂ) • (M z).submatrix j j) :
    IsPosFrame V H ∧ OneFormBound V (fun _ => 1) G (conn H) C ∧ TwoFormBound V H G (curv H) C := by
  have hN : IsPosFrame V fun x => (M x).submatrix j j :=
    ⟨hM.isOpen, fun a b => hM.smooth _ _, fun z hz => (hM.posDef z hz).submatrix hj⟩
  have hN' := hN.isHermFrame
  have hp : ∀ z ∈ V, (H z).PosDef := fun z hz => by
    rw [hH z hz]; exact (hN.posDef z hz).smul (by exact_mod_cast hc)
  have he : ∀ z ∈ V, H =ᶠ[𝓝 z] fun x => (c : ℂ) • (M x).submatrix j j := fun z hz =>
    mem_of_superset (hM.isOpen.mem_nhds hz) hH
  refine ⟨⟨hM.isOpen, fun a b => ((hN.smooth a b).const_smul (c : ℂ)).congr fun z hz => by rw [hH z hz]; rfl, hp⟩,
    fun z hz => ⟨PosDef.one, (h1 z hz).2.1, fun ξ => ?_⟩, fun z hz => ⟨hp z hz, (h1 z hz).2.1, fun ξ η => ?_⟩⟩
  · rw [conn_congr (he z hz), conn_const_smul hc.ne' (hN'.one hz) (hN'.isUnit z hz),
      conn_submatrix (hM.posDef z hz) hj (h0 z hz)]
    have h3 := opNorm_submatrix_le (PosDef.one (n := Fin g) (R := ℂ)) hj
      (fun s b hs => one_apply_ne fun h => hs ⟨b, h.symm⟩) (conn M z ξ)
    rw [submatrix_one _ hj] at h3
    exact h3.trans ((h1 z hz).2.2 ξ)
  · rw [curv_congr (he z hz), curv_const_smul hc.ne' (hN'.two hz) (hN'.isUnit z hz), curv_submatrix hj
      (mem_of_superset (hM.isOpen.mem_nhds hz) fun x hx => ⟨hM.posDef x hx, h0 x hx⟩), hH z hz]
    exact (opNorm_smul_metric_le (hN.posDef z hz) hc.le _).trans
      ((opNorm_submatrix_le (hM.posDef z hz) hj (h0 z hz) _).trans ((h2 z hz).2.2 ξ η))

theorem bounds_pullback {n : ℕ} {W : Set (Fin n → ℂ)} {Y : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {G' : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ} {φ : (Fin e → ℂ) → Fin n → ℂ} {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hV : IsOpen V) (hG : ∀ z ∈ V, (G z).PosSemidef) (hY : ∀ w ∈ W, MContDiffAt ∞ Y w)
    (h1 : OneFormBound W (fun _ => 1) G' (conn Y) C) (h2 : TwoFormBound W Y G' (curv Y) C)
    (hφ : ∀ z ∈ V, AnalyticAt ℂ φ z) (hW : ∀ z ∈ V, φ z ∈ W)
    (hS : ∀ z ∈ V, ∀ w, gnorm (G' (φ z)) (fderiv ℂ φ z w) ≤ D * gnorm (G z) w) :
    IsPosFrame V (fun x => Y (φ x)) ∧ OneFormBound V (fun _ => 1) G (conn fun x => Y (φ x)) (C * D ^ 2) ∧
      TwoFormBound V (fun x => Y (φ x)) G (curv fun x => Y (φ x)) (C * D ^ 2) := by
  have hp : ∀ z ∈ V, (Y (φ z)).PosDef := fun z hz => (h2 _ (hW z hz)).1
  refine ⟨⟨hV, fun a b z hz => ((hY _ (hW z hz) a b).comp z
    ((hφ z hz).contDiffAt.restrict_scalars ℝ)).contDiffWithinAt, hp⟩,
    fun z hz => ⟨PosDef.one, hG z hz, fun ξ => ?_⟩, fun z hz => ⟨hp z hz, hG z hz, fun ξ η => ?_⟩⟩
  · rw [conn_comp_holo ((hY _ (hW z hz)).of_le (by norm_cast)) (hφ z hz).differentiableAt]
    refine ((h1 _ (hW z hz)).2.2 _).trans ((mul_le_mul_of_nonneg_left (hS z hz ξ) hC).trans ?_)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by nlinarith) hC) (gnorm_nonneg _ _)
  · rw [curv_comp_holo ((hY _ (hW z hz)).of_le (by norm_cast)) ((isUnit_iff_isUnit_det _).1 (hp z hz).isUnit)
      (hφ z hz).contDiffAt]
    refine ((h2 _ (hW z hz)).2.2 _ _).trans ?_
    have := gnorm_nonneg (G z) ξ
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (hS z hz ξ) hC) (hS z hz η) (gnorm_nonneg _ _)
      (by positivity)).trans_eq (by ring)

end Bounds

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in

theorem blockModel_bounds : ∀ (e m : ℕ) (σ : Fin m → Option (Fin e)) (ι : Type) [Fintype ι] (μ : ι → ℕ) (ρ : ℝ) (U : Set (Fin e → ℂ)) (H : ∀ τ, (Fin e → ℂ) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ), 0 < ρ → punct σ ρ ⊆ U → IsBlockModel ρ U H → ∃ ρ' C : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ τ, GlobalTheory.HermFrame.IsPosFrame (punct σ ρ') (H τ) ∧ GlobalTheory.HermFrame.OneFormBound (punct σ ρ') (fun _ => (1 : Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ)) (modelGram σ) (GlobalTheory.HermFrame.conn (H τ)) C ∧ GlobalTheory.HermFrame.TwoFormBound (punct σ ρ') (H τ) (modelGram σ) (GlobalTheory.HermFrame.curv (H τ)) C := by
  intro e m σ ι _ μ ρ U H hρ hU ⟨n, k, hk, g, rk, τ₀, B, φ, Q, κ, hP, hφ, hφ0, hφ1, hQ, hcard, hli, hκ, hH⟩
  classical
  obtain ⟨ρ₁, c₀, C, hρ₁, hρ₁', -, -, -, h1, h2⟩ := GlobalTheory.HodgeChartRow.hodgeChartBounds_of_schur_lemW
    GlobalTheory.schur_block_lower_bound GlobalTheory.smul_inv_mul_posSemidef_uniform_bound n k g rk hk τ₀ B hP
  obtain ⟨ρ₂, D, hρ₂, hρ₂', hS⟩ := GlobalTheory.T.poincare_metric_bound_punctured_polydisc e m n k hk σ ρ φ hρ hφ hφ1 fun z hz => (hH z hz.1 (hU hz)).1
  let ε : (Σ τ, Fin (μ τ)) ≃ Fin g := Fintype.equivFinOfCardEq hcard
  let A : (Fin e → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun z => of fun l i => Q (ε.symm i).1 z (ε.symm i).2 l
  have hA : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ∀ i l, AnalyticAt ℂ (fun x => A x i l) z := fun z hz i l =>
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball (hQ _ _ _) z hz
  have hφa := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball hφ
  have hA0 : IsUnit (A 0).det := by
    rw [← det_transpose, ← isUnit_iff_isUnit_det, ← linearIndependent_rows_iff_isUnit]
    exact hli.comp ε.symm ε.symm.injective
  obtain ⟨b, hb0, hb⟩ := holo_local_bounds (hA 0 (Metric.mem_ball_self hρ)) hA0
  have hnear : ∀ᶠ z in 𝓝 (0 : Fin e → ℂ), ‖φ z‖ < ρ₁ :=
    (hφa 0 (Metric.mem_ball_self hρ)).continuousAt.norm.eventually_lt continuousAt_const (by simpa [hφ0] using hρ₁)
  obtain ⟨ρ₃, hρ₃, h3⟩ := Metric.eventually_nhds_iff_ball.1 (hb.and hnear)
  set ρ' := min (min ρ₂ ρ₃) 1 with hρ'
  have l2 : ρ' ≤ ρ₂ := (min_le_left _ _).trans (min_le_left _ _)
  have l3 : ρ' ≤ ρ₃ := (min_le_left _ _).trans (min_le_right _ _)
  have l0 : ρ' ≤ ρ := l2.trans hρ₂'
  have hV : ∀ z ∈ punct σ ρ', z ∈ Metric.ball (0 : Fin e → ℂ) ρ ∧ z ∈ U := fun z hz =>
    ⟨(punct_mono σ l0 hz).1, hU (punct_mono σ l0 hz)⟩
  have hH' := fun z (hz : z ∈ punct σ ρ') => hH z (hV z hz).1 (hV z hz).2
  obtain ⟨p0, p1, p2⟩ := bounds_pullback (V := punct σ ρ') (G := modelGram σ) (φ := φ) (le_max_right C 0)
    (le_max_right D 1) (isOpen_punct σ ρ') (fun z _ => modelGram_posSemidef σ z)
    (fun w hw => (GlobalTheory.HodgeGramLocal.hodgeGram_local n k g rk hk τ₀ B hP w
      ⟨fun i => (hw.1 i).trans_le (hρ₁'.trans (by norm_num)), hw.2⟩).1)
    (h1.mono (le_max_left _ _)) (h2.mono (le_max_left _ _)) (fun z hz => hφa z (hV z hz).1)
    (fun z hz => ⟨fun i => (norm_le_pi_norm _ i).trans_lt (h3 z (punct_mono σ l3 hz).1).2, (hH' z hz).1.2⟩)
    fun z hz w => (hS z (punct_mono σ l2 hz) w).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (gnorm_nonneg _ _))
  obtain ⟨q0, q1, q2⟩ := bounds_dual_changeFrame (A := A) (by positivity) hb0 p0 p1 p2
    (fun z hz => hA z (hV z hz).1) fun z hz => by
      obtain ⟨⟨a1, a2, a3, a4⟩, -⟩ := h3 z (punct_mono σ l3 hz).1
      exact ⟨a1, a2, a3, fun ξ => (a4 ξ).trans (mul_le_mul_of_nonneg_left
        (norm_le_gnorm_modelGram σ (punct_mono σ (min_le_right _ _) hz) ξ) hb0)⟩
  have hent : ∀ z ∈ punct σ ρ', ∀ (p p' : Σ τ, Fin (μ τ)),
      ((A z)ᵀ * dualGram (hodgeGram hk τ₀ B (φ z)) * (A z)ᴴᵀ) (ε p) (ε p') =
        (Q p.1 z * (hodgeGram hk τ₀ B (φ z))⁻¹ * (Q p'.1 z)ᴴ) p.2 p'.2 := fun z hz p p' => by
    have hs : (hodgeGram hk τ₀ B (φ z)).IsSymm := IsSymm.ext fun a c => by
      have hB : ∀ i, (B i c a : ℝ) = B i a c := fun i => by simpa using (hP.psd i).isHermitian.apply a c
      simp [hodgeGram, imPeriod, Matrix.sum_apply, hB, (hP.symm _ (hH' z hz).1.1).apply]
    rw [dualGram, transpose_nonsing_inv, hs.eq]
    simp only [mul_apply, transpose_apply, conjTranspose_apply, A, of_apply]
    rw [ε.symm_apply_apply, ε.symm_apply_apply]
  refine ⟨ρ', _, lt_min (lt_min hρ₂ hρ₃) one_pos, l0, fun τ => bounds_block (j := fun a => ε ⟨τ, a⟩) (hκ τ)
    (ε.injective.comp sigma_mk_injective) q0 (q1.mono (le_max_left _ _)) (q2.mono (le_max_right _ _))
    (fun z hz s a hs => ?_) fun z hz => ?_⟩
  · obtain ⟨⟨τ', a'⟩, rfl⟩ := ε.surjective s
    have hne : τ' ≠ τ := by rintro rfl; exact hs ⟨a', rfl⟩
    rw [hent z hz, (hH' z hz).2.2 τ' τ hne, Matrix.zero_apply]
  · rw [(hH' z hz).2.1 τ]
    congr 1
    ext a a'
    exact (hent z hz ⟨τ, a⟩ ⟨τ, a'⟩).symm

end GlobalTheory.CurvInterp.Block
