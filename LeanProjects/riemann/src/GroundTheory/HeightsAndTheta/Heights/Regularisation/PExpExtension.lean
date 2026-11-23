import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StRiemannSlices
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StPuncturedExpOrder
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StLogCoverDescent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Matrix

noncomputable section

namespace ExpQuad

theorem eq_of_continuousAt {n : ℕ} {F₁ F₂ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hz : z ∈ ball (0 : Fin n → ℂ) 1) (h₁ : ContinuousAt F₁ z) (h₂ : ContinuousAt F₂ z)
    (heq : ∀ y ∈ ball (0 : Fin n → ℂ) 1, (∀ i, y i ≠ 0) → F₁ y = F₂ y) : F₁ z = F₂ z := by
  let γ : ℝ → Fin n → ℂ := fun t k => z k + (t : ℂ)
  have hγc : Continuous γ := by
    refine continuous_pi fun k => ?_
    exact continuous_const.add Complex.continuous_ofReal
  have hγ0 : γ 0 = z := by funext k; simp [γ]
  have hγ : Tendsto γ (𝓝[>] 0) (𝓝 z) := by
    rw [← hγ0]
    exact (hγc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hball : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ ball (0 : Fin n → ℂ) 1 :=
    hγ.eventually (isOpen_ball.mem_nhds hz)
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, γ t k ≠ 0 := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : z k = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [γ, hk, zero_add, ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt ht
    · exact (((continuous_apply k).tendsto z).comp hγ).eventually_ne hk
  have e₁ : Tendsto (F₁ ∘ γ) (𝓝[>] 0) (𝓝 (F₁ z)) := h₁.tendsto.comp hγ
  have e₂ : Tendsto (F₂ ∘ γ) (𝓝[>] 0) (𝓝 (F₂ z)) := h₂.tendsto.comp hγ
  have e₁' : Tendsto (F₂ ∘ γ) (𝓝[>] 0) (𝓝 (F₁ z)) := by
    refine e₁.congr' ?_
    filter_upwards [hball, hne] with t h1 h2
    exact heq _ h1 h2
  exact tendsto_nhds_unique e₁' e₂

def qf {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) : ℂ :=
  (fun k => (v k : ℂ)) ⬝ᵥ A *ᵥ (fun k => (v k : ℂ))

theorem qf_add {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    qf (A + B) v = qf A v + qf B v := by
  simp [qf, Matrix.add_mulVec, dotProduct_add]

theorem qf_smul {g : ℕ} (c : ℂ) (A : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    qf (c • A) v = c * qf A v := by
  simp [qf, Matrix.smul_mulVec, dotProduct_smul]

theorem qf_sum {g : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    qf (∑ i ∈ s, A i) v = ∑ i ∈ s, qf (A i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qf]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, qf_add, ih]

theorem qf_intCast {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    qf (B.map (Int.cast : ℤ → ℂ)) v = ((intQuad B v : ℤ) : ℂ) := by
  simp [qf, intQuad, dotProduct, mulVec]

theorem analyticAt_finsetSum {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → (Fin n → ℂ) → ℂ}
    {w : Fin n → ℂ} (h : ∀ i ∈ s, AnalyticAt ℂ (f i) w) :
    AnalyticAt ℂ (fun x => ∑ i ∈ s, f i x) w := by
  have := Finset.analyticAt_sum s h
  convert this using 1
  funext x
  simp [Finset.sum_apply]

theorem analyticAt_coord_div_mul {n : ℕ} (k : Fin n) (c d : ℂ) (w : Fin n → ℂ) :
    AnalyticAt ℂ (fun x : Fin n → ℂ => x k / c * d) w := by
  refine ((analyticAt_coord_div_add k c 0 w).mul (analyticAt_const (v := d))).congr ?_
  exact Filter.Eventually.of_forall fun x => by simp

variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)

theorem cusp_ne {i j : Fin a} (h : i ≠ j) : Fin.castLE P.a_le i ≠ Fin.castLE P.a_le j :=
  fun e => h (Fin.castLE_injective _ e)

theorem qf_tau (w : Fin n → ℂ) :
    qf (P.τ w) v = qf (P.tau0 w) v +
      ∑ i, w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) * ((intQuad (P.B i) v : ℤ) : ℂ) := by
  have h : P.τ w = P.tau0 w + ∑ i : Fin a, (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) •
      (P.B i).map (Int.cast : ℤ → ℂ) := by
    simp [PeriodPolydisc.tau0]
  rw [h, qf_add, qf_sum]
  simp [qf_smul, qf_intCast]

theorem tau_shifted_periodic (j : Fin a) (w : Fin n → ℂ) (hw : w ∈ logCover P.a_le) :
    P.tau0 (w + Pi.single (Fin.castLE P.a_le j) (2 * Real.pi * Complex.I)) = P.tau0 w := by
  have key : ∀ i : Fin a,
      ((w + Pi.single (Fin.castLE P.a_le j) (2 * Real.pi * Complex.I) : Fin n → ℂ) (Fin.castLE P.a_le i) /
          (2 * Real.pi * Complex.I)) • (P.B i).map (Int.cast : ℤ → ℂ) =
        (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) • (P.B i).map (Int.cast : ℤ → ℂ) +
          (Pi.single j ((P.B j).map (Int.cast : ℤ → ℂ)) : Fin a → Matrix (Fin g) (Fin g) ℂ) i := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [Pi.add_apply, Pi.single_eq_same, add_div, div_self two_pi_I_ne_zero, add_smul,
        one_smul]
    · simp [cusp_ne P hij, hij]
  simp only [PeriodPolydisc.tau0, P.periodic j w hw]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_pi_single']
  simp only [Finset.mem_univ, if_true]
  abel

def phi (w : Fin n → ℂ) : ℂ := 2 * Real.pi * Complex.I * qf (P.tau0 w) v

theorem tau_shifted_entry (w : Fin n → ℂ) (p q : Fin g) :
    P.tau0 w p q = P.τ w p q - ∑ i, w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) *
      ((P.B i p q : ℤ) : ℂ) := by
  simp [PeriodPolydisc.tau0, Matrix.sub_apply, Matrix.sum_apply]

theorem phi_analytic : AnalyticOnNhd ℂ (phi P v) (logCover P.a_le) := by
  intro w hw
  have he : ∀ p q, AnalyticAt ℂ (fun x => P.tau0 x p q) w := by
    intro p q
    simp only [tau_shifted_entry]
    exact (P.analytic p q w hw).sub
      (analyticAt_finsetSum _ fun i _ => analyticAt_coord_div_mul _ _ _ w)
  have hq : AnalyticAt ℂ (fun x => qf (P.tau0 x) v) w := by
    simp only [qf, dotProduct, mulVec]
    refine analyticAt_finsetSum _ fun p _ => analyticAt_const.mul ?_
    exact analyticAt_finsetSum _ fun q _ => (he p q).mul analyticAt_const
  exact analyticAt_const.mul hq

theorem phi_periodic (j : Fin a) (w : Fin n → ℂ) (hw : w ∈ logCover P.a_le) :
    phi P v (w + Pi.single (Fin.castLE P.a_le j) (2 * Real.pi * Complex.I)) = phi P v w := by
  simp only [phi, tau_shifted_periodic P j w hw]

theorem exp_quad (w : Fin n → ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * qf (P.τ w) v) =
      Complex.exp (phi P v w) *
        Complex.exp (∑ i, w (Fin.castLE P.a_le i) * ((intQuad (P.B i) v : ℤ) : ℂ)) := by
  rw [qf_tau, mul_add, Complex.exp_add, phi, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp [two_pi_I_ne_zero]

theorem norm_exp_quad_le (w : Fin n → ℂ) (hw : w ∈ logCover P.a_le) :
    ‖Complex.exp (2 * Real.pi * Complex.I * qf (P.τ w) v)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hpos := (P.im_posDef w hw).posSemidef.dotProduct_mulVec_nonneg (fun k => (v k : ℝ))
  have him : (qf (P.τ w) v).im =
      star (fun k => (v k : ℝ)) ⬝ᵥ ((P.τ w).map Complex.im *ᵥ fun k => (v k : ℝ)) := by
    simp [qf, dotProduct, mulVec, Complex.im_sum, Complex.mul_im, Complex.re_sum]
  have hre : (2 * Real.pi * Complex.I * qf (P.τ w) v).re = -(2 * Real.pi * (qf (P.τ w) v).im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, him]
  have := Real.pi_pos
  nlinarith

theorem norm_lt_one_of_mem_ball {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (k : Fin n) :
    ‖z k‖ < 1 :=
  (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.mp hz)

theorem mem_ball_of_forall {z : Fin n → ℂ} (h : ∀ k, ‖z k‖ < 1) : z ∈ ball (0 : Fin n → ℂ) 1 :=
  mem_ball_zero_iff.mpr ((pi_norm_lt_iff one_pos).mpr h)

theorem logLift_castLE (z : Fin n → ℂ) (i : Fin a) :
    logLift a z (Fin.castLE P.a_le i) = Complex.log (z (Fin.castLE P.a_le i)) := by
  simp [logLift, i.isLt]

theorem expCover_castLE (w : Fin n → ℂ) (i : Fin a) :
    expCover a w (Fin.castLE P.a_le i) = Complex.exp (w (Fin.castLE P.a_le i)) := by
  simp [expCover, i.isLt]

theorem logLift_mem {z : Fin n → ℂ} (hz : z ∈ puncturedChart P.a_le (ball 0 1)) :
    logLift a z ∈ logCover P.a_le := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · rw [logLift_castLE P, Complex.log_re]
    have h0 : z (Fin.castLE P.a_le i) ≠ 0 := hz.2 i
    exact Real.log_neg (norm_pos_iff.mpr h0) (norm_lt_one_of_mem_ball hz.1 _)
  · have : ¬ k.val < a := not_lt.mpr hk
    simp only [logLift, this, if_false]
    exact norm_lt_one_of_mem_ball hz.1 k

theorem expCover_mem {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) :
    expCover a w ∈ puncturedChart P.a_le (ball 0 1) := by
  refine ⟨mem_ball_of_forall fun k => ?_, fun j => ?_⟩
  · by_cases hk : k.val < a
    · have hk' : Fin.castLE P.a_le ⟨k.val, hk⟩ = k := Fin.ext rfl
      have h1 := hw.1 ⟨k.val, hk⟩
      rw [hk'] at h1
      simp only [expCover, hk, if_true, Complex.norm_exp]
      exact (Real.exp_lt_exp.mpr h1).trans_eq Real.exp_zero
    · simp only [expCover, hk, if_false]
      exact hw.2 k (not_lt.mp hk)
  · show expCover a w (Fin.castLE P.a_le j) ≠ 0
    rw [expCover_castLE P]
    exact Complex.exp_ne_zero _

def psi (z : Fin n → ℂ) : ℂ := phi P v (logLift a z)

theorem update_mem {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (i : Fin a)
    (hne : ∀ j : Fin a, j ≠ i → z (Fin.castLE P.a_le j) ≠ 0) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) 1 \ {0}) :
    Function.update z (Fin.castLE P.a_le i) x ∈ puncturedChart P.a_le (ball 0 1) := by
  classical
  refine ⟨mem_ball_of_forall fun k => ?_, fun j => ?_⟩
  · by_cases hk : k = Fin.castLE P.a_le i
    · subst hk
      simp only [Function.update_self]
      simpa using hx.1
    · rw [Function.update_of_ne hk]
      exact norm_lt_one_of_mem_ball hz k
  · show Function.update z (Fin.castLE P.a_le i) x (Fin.castLE P.a_le j) ≠ 0
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      exact hx.2
    · rw [Function.update_of_ne (cusp_ne P hj)]
      exact hne j hj

theorem slice_order (hD : LogCoverDescent.Statement) (hO : PuncturedExpOrder.Statement)
    {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (i : Fin a)
    (hne : ∀ j : Fin a, j ≠ i → z (Fin.castLE P.a_le j) ≠ 0) :
    0 ≤ intQuad (P.B i) v ∧ ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun x => Complex.exp (psi P v (Function.update z (Fin.castLE P.a_le i) x)))
        (𝓝[≠] 0) (𝓝 c) := by
  classical
  have hΨ := (hD n a P.a_le (phi P v) (phi_analytic P v) (phi_periodic P v)).1
  set C : ℂ := ∏ j ∈ Finset.univ.erase i, z (Fin.castLE P.a_le j) ^ intQuad (P.B j) v with hC
  have hC0 : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj =>
    zpow_ne_zero _ (hne j (Finset.ne_of_mem_erase hj))
  have hCpos : 0 < ‖C‖ := norm_pos_iff.mpr hC0
  refine hO 1 (fun x => psi P v (Function.update z (Fin.castLE P.a_le i) x)) (intQuad (P.B i) v)
    ‖C‖⁻¹ one_pos ?_ ?_
  · intro x hx
    have hy := update_mem P hz i hne hx
    exact ((hΨ _ hy).differentiableAt.comp x
      (hasFDerivAt_update z x).differentiableAt).differentiableWithinAt
  · intro x hx
    have hy := update_mem P hz i hne hx
    have hw := logLift_mem P hy
    have hb := norm_exp_quad_le P v _ hw
    rw [exp_quad] at hb
    have hprod : Complex.exp (∑ j, logLift a (Function.update z (Fin.castLE P.a_le i) x)
        (Fin.castLE P.a_le j) * ((intQuad (P.B j) v : ℤ) : ℂ)) = x ^ intQuad (P.B i) v * C := by
      rw [Complex.exp_sum]
      have hj : ∀ j, Complex.exp (logLift a (Function.update z (Fin.castLE P.a_le i) x)
          (Fin.castLE P.a_le j) * ((intQuad (P.B j) v : ℤ) : ℂ)) =
          Function.update z (Fin.castLE P.a_le i) x (Fin.castLE P.a_le j) ^ intQuad (P.B j) v := by
        intro j
        rw [logLift_castLE P, mul_comm, Complex.exp_int_mul,
          Complex.exp_log (show Function.update z (Fin.castLE P.a_le i) x (Fin.castLE P.a_le j) ≠ 0
            from hy.2 j)]
      simp only [hj]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hC]
      congr 1
      · simp
      · refine Finset.prod_congr rfl fun j hj' => ?_
        rw [Function.update_of_ne (cusp_ne P (Finset.ne_of_mem_erase hj'))]
    rw [hprod, ← mul_assoc, norm_mul] at hb
    have hb' : ‖Complex.exp (psi P v (Function.update z (Fin.castLE P.a_le i) x)) *
        x ^ intQuad (P.B i) v‖ * ‖C‖ ≤ 1 := hb
    simpa [one_div] using (le_div_iff₀ hCpos).mpr hb'

theorem slice_noncusp {F : (Fin n → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (puncturedChart P.a_le (ball 0 1)))
    {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (m : Fin n) (hm : ¬ m.val < a)
    (hne : ∀ j, j ≠ m → z j ≠ 0) :
    ∃ c : ℂ, Tendsto (fun x => F (Function.update z m x)) (𝓝[≠] 0) (𝓝 c) := by
  classical
  have hmem : Function.update z m 0 ∈ puncturedChart P.a_le (ball 0 1) := by
    refine ⟨mem_ball_of_forall fun k => ?_, fun j => ?_⟩
    · by_cases hk : k = m
      · subst hk
        simp
      · rw [Function.update_of_ne hk]
        exact norm_lt_one_of_mem_ball hz k
    · have hjm : Fin.castLE P.a_le j ≠ m := by
        intro e
        apply hm
        rw [← e, Fin.val_castLE]
        exact j.isLt
      show Function.update z m 0 (Fin.castLE P.a_le j) ≠ 0
      rw [Function.update_of_ne hjm]
      exact hne _ hjm
  refine ⟨F (Function.update z m 0), ?_⟩
  have hc : Continuous (fun x : ℂ => Function.update z m x) :=
    (continuous_const (y := z)).update m (continuous_id (X := ℂ))
  exact ((hF _ hmem).continuousAt.tendsto.comp (hc.tendsto 0)).mono_left nhdsWithin_le_nhds

end ExpQuad

open ExpQuad in

theorem ExpQuadMonomial.proof (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    ExpQuadMonomial.Statement := by
  intro n a g P v
  classical
  obtain ⟨hΨ, hdesc⟩ := hD n a P.a_le (phi P v) (phi_analytic P v) (phi_periodic P v)
  have hΨ' : AnalyticOnNhd ℂ (psi P v) (puncturedChart P.a_le (ball 0 1)) := hΨ
  have hk : ∀ i, 0 ≤ intQuad (P.B i) v := fun i =>
    (slice_order P v hD hO (z := fun _ => (1 / 2 : ℂ))
      (mem_ball_of_forall fun _ => by norm_num) i (fun _ _ => by norm_num)).1
  have hsl : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ m : Fin n, (∀ j, j ≠ m → z j ≠ 0) → m.val < a →
      ∃ c : ℂ, c ≠ 0 ∧
        Tendsto (fun x => Complex.exp (psi P v (Function.update z m x))) (𝓝[≠] 0) (𝓝 c) := by
    intro z hz m hne hm
    have hmi : Fin.castLE P.a_le (⟨m.val, hm⟩ : Fin a) = m := Fin.ext rfl
    have := (slice_order P v hD hO hz ⟨m.val, hm⟩
      (fun j hj => hne _ (by rw [← hmi]; exact cusp_ne P hj))).2
    rwa [hmi] at this
  let G : (Fin n → ℂ) → ℂ := fun z => Complex.exp (psi P v z)
  let H : (Fin n → ℂ) → ℂ := fun z => Complex.exp (-psi P v z)
  have hGa : AnalyticOnNhd ℂ G (puncturedChart P.a_le (ball 0 1)) := fun z hz => (hΨ' z hz).cexp
  have hHa : AnalyticOnNhd ℂ H (puncturedChart P.a_le (ball 0 1)) :=
    fun z hz => (hΨ' z hz).neg.cexp
  have hWsub : ∀ z ∈ ball (0 : Fin n → ℂ) 1 ∩ {z | ∀ i, z i ≠ 0},
      z ∈ puncturedChart P.a_le (ball 0 1) :=
    fun z hz => ⟨hz.1, fun j => hz.2 _⟩
  obtain ⟨G', hG'a, hG'eq⟩ := hE n G
    (fun z hz => (hGa z (hWsub z hz)).differentiableAt.differentiableWithinAt)
    (fun z hz m hne => by
      by_cases hm : m.val < a
      · obtain ⟨c, -, hc⟩ := hsl z hz m hne hm
        exact ⟨c, hc⟩
      · exact slice_noncusp P hGa hz m hm hne)
  obtain ⟨H', hH'a, hH'eq⟩ := hE n H
    (fun z hz => (hHa z (hWsub z hz)).differentiableAt.differentiableWithinAt)
    (fun z hz m hne => by
      by_cases hm : m.val < a
      · obtain ⟨c, hc0, hc⟩ := hsl z hz m hne hm
        refine ⟨c⁻¹, ?_⟩
        simpa [H, Complex.exp_neg] using hc.inv₀ hc0
      · exact slice_noncusp P hHa hz m hm hne)
  refine ⟨hk, G', hG'a, fun z hz => ?_, fun w hw => ?_⟩
  · have h1 : G' z * H' z = 1 := eq_of_continuousAt (F₁ := fun y => G' y * H' y) (F₂ := fun _ => 1) hz
      ((hG'a z hz).continuousAt.mul (hH'a z hz).continuousAt) continuousAt_const
      (fun y hy hyW => by
        simp only [hG'eq y hy hyW, hH'eq y hy hyW, G, H, ← Complex.exp_add, add_neg_cancel,
          Complex.exp_zero])
    exact left_ne_zero_of_mul_eq_one h1
  · have hy := expCover_mem P hw
    have h1 : G' (expCover a w) = G (expCover a w) :=
      eq_of_continuousAt hy.1 (hG'a _ hy.1).continuousAt (hGa _ hy).continuousAt hG'eq
    have h2 : G (expCover a w) = Complex.exp (phi P v w) := by
      simp only [G, psi]
      rw [hdesc w hw]
    change Complex.exp (2 * Real.pi * Complex.I * qf (P.τ w) v) = _
    rw [exp_quad P v w, h1, h2, mul_comm]
    congr 1
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [expCover_castLE P, ← Complex.exp_nat_mul, mul_comm]
    congr 2
    exact_mod_cast (Int.toNat_of_nonneg (hk i)).symm

end

end GroundTheory.Heights₂.Heights.Regular
