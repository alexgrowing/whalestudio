import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Matrix Topology Filter

noncomputable section

theorem analyticAt_of_exp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g h : E → ℂ}
    {z₀ : E} (hg : ContinuousAt g z₀) (hh : AnalyticAt ℂ h z₀)
    (he : ∀ᶠ z in 𝓝 z₀, Complex.exp (g z) = h z) : AnalyticAt ℂ g z₀ := by
  have e₀ : Complex.exp (g z₀) = h z₀ := he.self_of_nhds
  have h0 : h z₀ ≠ 0 := e₀ ▸ Complex.exp_ne_zero _
  set L : E → ℂ := fun z => g z₀ + Complex.log (h z / h z₀) with hLdef
  have hL : AnalyticAt ℂ L z₀ := by
    refine analyticAt_const.add ((hh.div analyticAt_const h0).clog ?_)
    simp [h0]
  refine hL.congr ?_
  have hLz : L z₀ = g z₀ := by simp [hLdef, h0]
  have hg' : ∀ᶠ z in 𝓝 z₀, ‖g z - g z₀‖ < Real.pi := by
    have := hg.eventually (Metric.ball_mem_nhds (g z₀) Real.pi_pos)
    filter_upwards [this] with z hz
    simpa [dist_eq_norm] using hz
  have hL' : ∀ᶠ z in 𝓝 z₀, ‖L z - g z₀‖ < Real.pi := by
    have := hL.continuousAt.eventually (Metric.ball_mem_nhds (L z₀) Real.pi_pos)
    filter_upwards [this] with z hz
    simpa [dist_eq_norm, hLz] using hz
  filter_upwards [hg', hL', he] with z hgz hLz' hez
  have hz0 : h z ≠ 0 := hez ▸ Complex.exp_ne_zero _
  have hexp : Complex.exp (L z) = Complex.exp (g z) := by
    simp only [hLdef, Complex.exp_add, e₀, hez]
    rw [Complex.exp_log (div_ne_zero hz0 h0)]
    field_simp
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hnorm : ‖(m : ℂ) * (2 * Real.pi * Complex.I)‖ < 2 * Real.pi := by
    have : (m : ℂ) * (2 * Real.pi * Complex.I) = (L z - g z₀) - (g z - g z₀) := by rw [hm]; ring
    rw [this]
    calc ‖(L z - g z₀) - (g z - g z₀)‖ ≤ ‖L z - g z₀‖ + ‖g z - g z₀‖ := norm_sub_le _ _
      _ < 2 * Real.pi := by linarith
  have hm0 : m = 0 := by
    have hpi := Real.pi_pos
    simp only [norm_mul, Complex.norm_intCast, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi] at hnorm
    have h1 : |(m : ℝ)| < 1 := by nlinarith
    rw [← Int.cast_abs] at h1
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
  rw [hm, hm0]
  simp

theorem exists_analytic_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E}
    (hU : IsOpen U) (hc : Convex ℝ U) (hne : U.Nonempty) {h : E → ℂ} (hh : AnalyticOnNhd ℂ h U)
    (h0 : ∀ z ∈ U, h z ≠ 0) :
    ∃ G : E → ℂ, AnalyticOnNhd ℂ G U ∧ ∀ z ∈ U, Complex.exp (G z) = h z := by
  have : ContractibleSpace U := hc.contractibleSpace hne
  have : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  obtain ⟨z₀, hz₀⟩ := hne
  let f : C(U, ℂ) := ⟨U.domRestrict h, hh.continuousOn.domRestrict⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (a₀ := ⟨z₀, hz₀⟩) (e₀ := Complex.log (h z₀))
    (by simp [f, Complex.exp_log (h0 z₀ hz₀)]) (fun x => h0 x x.2)
  classical
  let G : E → ℂ := fun z => if hz : z ∈ U then F ⟨z, hz⟩ else 0
  have hGe : ∀ z ∈ U, Complex.exp (G z) = h z := fun z hz => by
    simpa [G, hz, f] using congrFun hF ⟨z, hz⟩
  have hGc : ContinuousOn G U := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert F.continuous using 1
    funext x
    simp [G, x.2]
  refine ⟨G, fun z hz => analyticAt_of_exp_eq (hGc.continuousAt (hU.mem_nhds hz)) (hh z hz) ?_, hGe⟩
  filter_upwards [hU.mem_nhds hz] with y hy using hGe y hy

theorem eqOn_of_exp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set E}
    (hW : IsOpen W) (hc : Convex ℝ W) {g₁ g₂ : E → ℂ} (h₁ : ContinuousOn g₁ W)
    (h₂ : ContinuousOn g₂ W) (he : ∀ w ∈ W, Complex.exp (g₁ w) = Complex.exp (g₂ w)) {w₀ : E}
    (hw₀ : w₀ ∈ W) (h₀ : g₁ w₀ = g₂ w₀) : ∀ w ∈ W, g₁ w = g₂ w := by
  have : ContractibleSpace W := hc.contractibleSpace ⟨w₀, hw₀⟩
  have : LocallyPathConnectedSpace W := hW.locallyPathConnectedSpace
  let f : C(W, ℂ) := ⟨fun x => Complex.exp (g₁ x), Complex.continuous_exp.comp h₁.domRestrict⟩
  obtain ⟨F, -, huniq⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (a₀ := ⟨w₀, hw₀⟩) (e₀ := g₁ w₀) rfl (fun x => Complex.exp_ne_zero _)
  have e₁ := huniq ⟨W.domRestrict g₁, h₁.domRestrict⟩ ⟨rfl, rfl⟩
  have e₂ := huniq ⟨W.domRestrict g₂, h₂.domRestrict⟩
    ⟨h₀.symm, funext fun x => (he x x.2).symm⟩
  intro w hw
  exact congrArg (fun F : C(W, ℂ) => F ⟨w, hw⟩) (e₁.trans e₂.symm)

theorem isOpen_logCover {n a : ℕ} (h : a ≤ n) : IsOpen (logCover h) := by
  have h1 : IsOpen {w : Fin n → ℂ | ∀ i : Fin a, (w (Fin.castLE h i)).re < 0} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const
  have h2 : IsOpen {w : Fin n → ℂ | ∀ k : Fin n, a ≤ k.val → ‖w k‖ < 1} := by
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun k => ?_
    by_cases hk : a ≤ k.val
    · simp only [hk, Set.iInter_true]
      exact isOpen_lt (f := fun w : Fin n → ℂ => ‖w k‖) (by fun_prop) continuous_const
    · simp [hk]
  exact h1.inter h2

theorem convex_logCover {n a : ℕ} (h : a ≤ n) : Convex ℝ (logCover h) := by
  intro x hx y hy s t hs ht hst
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have := convex_Iio (0 : ℝ) (hx.1 i) (hy.1 i) hs ht hst
    simpa using this
  · have := convex_ball (0 : ℂ) 1 (mem_ball_zero_iff.2 (hx.2 k hk))
      (mem_ball_zero_iff.2 (hy.2 k hk)) hs ht hst
    simpa using this

theorem logCover_nonempty {n a : ℕ} (h : a ≤ n) : (logCover h).Nonempty :=
  ⟨fun k => if k.val < a then -1 else 0,
    fun i => by simp [Fin.castLE, i.isLt], fun k hk => by simp [not_lt.2 hk]⟩

theorem continuous_expCover {n : ℕ} (a : ℕ) : Continuous (expCover (n := n) a) :=
  continuous_pi fun k => by
    unfold expCover
    split_ifs
    exacts [Complex.continuous_exp.comp (continuous_apply k), continuous_apply k]

theorem expCover_mem_ball {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    expCover a w ∈ ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro k
  by_cases hk : k.val < a
  · have hre := hw.1 ⟨k.val, hk⟩
    have hkk : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
    rw [hkk] at hre
    simp only [expCover, hk, if_true, Complex.norm_exp]
    simpa using Real.exp_lt_exp.mpr hre
  · simp only [expCover, hk, if_false]
    exact hw.2 k (not_lt.1 hk)

theorem expCover_castLE {n a : ℕ} (h : a ≤ n) (w : Fin n → ℂ) (i : Fin a) :
    expCover a w (Fin.castLE h i) = Complex.exp (w (Fin.castLE h i)) := by
  simp [expCover, i.isLt]

theorem intQuad_cast {R : Type*} [CommRing R] {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    ((intQuad B v : ℤ) : R) = (fun k => (v k : R)) ⬝ᵥ B.map (Int.cast : ℤ → R) *ᵥ fun k => (v k : R) := by
  simp only [intQuad, dotProduct, mulVec, map_apply]
  push_cast
  rfl

theorem posSemidef_of_intQuad_nonneg {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (hB : Bᵀ = B)
    (h : ∀ v, 0 ≤ intQuad B v) : (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · change (B.map (Int.cast : ℤ → ℝ))ᴴ = _
    rw [conjTranspose, ← transpose_map, hB]
    ext i j
    simp
  rw [star_trivial]
  set M := B.map (Int.cast : ℤ → ℝ)
  set q : (Fin g → ℝ) → ℝ := fun y => y ⬝ᵥ M *ᵥ y with hq
  have hqc : Continuous q := by
    simp only [hq, dotProduct, mulVec]
    fun_prop
  let m : ℕ → Fin g → ℤ := fun N k => ⌊(N : ℝ) * x k⌋
  let y : ℕ → Fin g → ℝ := fun N => ((N : ℝ)⁻¹) • fun k => ((m N k : ℤ) : ℝ)
  have hy : Tendsto y atTop (𝓝 x) := by
    refine tendsto_pi_nhds.2 fun k => ?_
    have hlow : Tendsto (fun N : ℕ => x k - 1 / (N : ℝ)) atTop (𝓝 (x k)) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x k) atTop (𝓝 (x k))).sub
        tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have := Int.lt_floor_add_one ((N : ℝ) * x k)
      simp only [y, m, Pi.smul_apply, smul_eq_mul]
      rw [sub_le_iff_le_add, one_div, ← mul_add_one, inv_mul_eq_div, le_div_iff₀ hN']
      nlinarith
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have := Int.floor_le ((N : ℝ) * x k)
      simp only [y, m, Pi.smul_apply, smul_eq_mul]
      rw [inv_mul_eq_div, div_le_iff₀ hN']
      linarith
  have hnn : ∀ N, 0 ≤ q (y N) := fun N => by
    simp only [hq, y, smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul]
    have := intQuad_cast (R := ℝ) B (m N)
    rw [← this, ← mul_assoc]
    exact mul_nonneg (mul_self_nonneg _) (by exact_mod_cast h (m N))
  exact ge_of_tendsto' ((hqc.tendsto x).comp hy) hnn

namespace PeriodPolydisc

variable {n a g : ℕ} (P : PeriodPolydisc n a g)

theorem quadratic_tau_shifted (v : Fin g → ℤ) (w : Fin n → ℂ) :
    (fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ (fun k => (v k : ℂ)) =
      (fun k => (v k : ℂ)) ⬝ᵥ P.τ w *ᵥ (fun k => (v k : ℂ)) -
        ∑ i : Fin a, w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) *
          ((intQuad (P.B i) v : ℤ) : ℂ) := by
  simp only [tau0, sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum, smul_mulVec,
    dotProduct_smul, smul_eq_mul, intQuad_cast]

theorem exp_quadratic_tau_shifted (v : Fin g → ℤ) (hnn : ∀ i, 0 ≤ intQuad (P.B i) v) (h : (Fin n → ℂ) → ℂ)
    (w : Fin n → ℂ)
    (hw : Complex.exp (2 * Real.pi * Complex.I *
        ((fun k => (v k : ℂ)) ⬝ᵥ P.τ w *ᵥ fun k => (v k : ℂ))) =
      (∏ i : Fin a, expCover a w (Fin.castLE P.a_le i) ^ (intQuad (P.B i) v).toNat) *
        h (expCover a w)) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ fun k => (v k : ℂ))) = h (expCover a w) := by
  have hk : ∀ i, ((intQuad (P.B i) v : ℤ) : ℂ) = (((intQuad (P.B i) v).toNat : ℕ) : ℂ) := fun i => by
    exact_mod_cast (Int.toNat_of_nonneg (hnn i)).symm
  have hprod : ∏ i : Fin a, expCover a w (Fin.castLE P.a_le i) ^ (intQuad (P.B i) v).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [expCover_castLE]
      exact pow_ne_zero _ (Complex.exp_ne_zero _)
  have hsum : Complex.exp (2 * Real.pi * Complex.I * ∑ i : Fin a,
      w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) * ((intQuad (P.B i) v : ℤ) : ℂ)) =
      ∏ i : Fin a, expCover a w (Fin.castLE P.a_le i) ^ (intQuad (P.B i) v).toNat := by
    rw [Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [expCover_castLE, ← Complex.exp_nat_mul, hk i]
    congr 1
    field_simp [two_pi_I_ne_zero]
  rw [quadratic_tau_shifted, mul_sub, Complex.exp_sub, hw, hsum]
  field_simp

theorem tau_shifted_transpose {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) : (P.tau0 w)ᵀ = P.tau0 w := by
  simp only [tau0, transpose_sub, transpose_sum, transpose_smul, ← transpose_map, P.B_symm,
    P.symm w hw]

theorem exists_quad_ext (h0 : ExpQuadMonomial.Statement) (v : Fin g → ℤ) :
    ∃ Q : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Q (ball 0 1) ∧ ∀ w ∈ logCover P.a_le,
      Q (expCover a w) = (fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ fun k => (v k : ℂ) := by
  obtain ⟨hnn, h, hha, hh0, hhe⟩ := h0 n a g P v
  obtain ⟨G, hGa, hGe⟩ := exists_analytic_log isOpen_ball (convex_ball 0 1)
    ⟨0, mem_ball_self one_pos⟩ hha hh0
  set F : (Fin n → ℂ) → ℂ := fun w =>
    2 * Real.pi * Complex.I * ((fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ fun k => (v k : ℂ)) with hFdef
  have hFe : ∀ w ∈ logCover P.a_le, Complex.exp (F w) = h (expCover a w) := fun w hw =>
    P.exp_quadratic_tau_shifted v hnn h w (hhe w hw)
  have hent : ∀ p q, ContinuousOn (fun w => P.tau0 w p q) (logCover P.a_le) := fun p q => by
    have : (fun w => P.tau0 w p q) = fun w => P.τ w p q - ∑ i : Fin a,
        w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) * ((P.B i p q : ℤ) : ℂ) := by
      funext w
      simp [tau0, Matrix.sum_apply]
    rw [this]
    exact (P.analytic p q).continuousOn.sub (continuousOn_finsetSum _ fun i _ =>
      (((continuous_apply _).continuousOn).div_const _).mul continuousOn_const)
  have hFc : ContinuousOn F (logCover P.a_le) := by
    simp only [hFdef, dotProduct, mulVec]
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun p _ => continuousOn_const.mul
      (continuousOn_finsetSum _ fun q _ => (hent p q).mul continuousOn_const))
  have hmaps : Set.MapsTo (expCover a) (logCover P.a_le) (ball 0 1) := fun w hw =>
    expCover_mem_ball P.a_le hw
  obtain ⟨w₀, hw₀⟩ := logCover_nonempty P.a_le
  set c := F w₀ - G (expCover a w₀) with hc
  have hGc : ContinuousOn (fun w => G (expCover a w) + c) (logCover P.a_le) :=
    (hGa.continuousOn.comp (continuous_expCover a).continuousOn hmaps).add continuousOn_const
  have key := eqOn_of_exp_eq (isOpen_logCover P.a_le) (convex_logCover P.a_le) hFc hGc
    (fun w hw => by
      rw [Complex.exp_add, hc, Complex.exp_sub, hGe _ (hmaps hw), hGe _ (hmaps hw₀), hFe w hw,
        hFe w₀ hw₀]
      field_simp [hh0 _ (hmaps hw₀)])
    hw₀ (by rw [hc]; ring)
  refine ⟨fun z => (G z + c) / (2 * Real.pi * Complex.I),
    (hGa.add analyticOnNhd_const).div analyticOnNhd_const fun _ _ => two_pi_I_ne_zero,
    fun w hw => ?_⟩
  simp only
  rw [← key w hw, hFdef]
  field_simp [two_pi_I_ne_zero]

end PeriodPolydisc

theorem polarise {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (hM : Mᵀ = M) (p q : Fin g) :
    (((fun k => ((Pi.single p 1 + Pi.single q 1 : Fin g → ℤ) k : ℂ)) ⬝ᵥ
          M *ᵥ fun k => ((Pi.single p 1 + Pi.single q 1 : Fin g → ℤ) k : ℂ)) -
        ((fun k => ((Pi.single p 1 : Fin g → ℤ) k : ℂ)) ⬝ᵥ
          M *ᵥ fun k => ((Pi.single p 1 : Fin g → ℤ) k : ℂ)) -
        ((fun k => ((Pi.single q 1 : Fin g → ℤ) k : ℂ)) ⬝ᵥ
          M *ᵥ fun k => ((Pi.single q 1 : Fin g → ℤ) k : ℂ))) / 2 = M p q := by
  have hc : ∀ r : Fin g, (fun k => ((Pi.single r 1 : Fin g → ℤ) k : ℂ)) = Pi.single r 1 := fun r => by
    funext k
    by_cases hk : k = r
    · subst hk; simp
    · simp [hk]
  have hadd : (fun k => ((Pi.single p 1 + Pi.single q 1 : Fin g → ℤ) k : ℂ)) =
      Pi.single p 1 + Pi.single q 1 := by
    rw [← hc p, ← hc q]
    funext k
    simp
  have hqp : M q p = M p q := by
    have := congrFun (congrFun hM p) q
    simpa [transpose_apply] using this
  rw [hadd, hc p, hc q]
  simp only [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single_one, single_one_dotProduct,
    col_apply, hqp]
  ring

theorem Tau0Holomorphic.proof (h0 : ExpQuadMonomial.Statement) : Tau0Holomorphic.Statement := by
  intro n a g P
  refine ⟨fun i => posSemidef_of_intQuad_nonneg (P.B i) (P.B_symm i) fun v => (h0 n a g P v).1 i,
    ?_⟩
  choose Q hQa hQe using P.exists_quad_ext h0
  refine ⟨fun z p q => (Q (Pi.single p 1 + Pi.single q 1) z - Q (Pi.single p 1) z -
      Q (Pi.single q 1) z) / 2, fun p q => ?_, fun w hw => ?_⟩
  · exact (((hQa _).sub (hQa _)).sub (hQa _)).div analyticOnNhd_const fun _ _ => two_ne_zero
  · ext p q
    simp only [hQe _ w hw]
    exact (polarise _ (P.tau_shifted_transpose hw) p q).symm

end

end GroundTheory.Heights₂.Heights.Regular
