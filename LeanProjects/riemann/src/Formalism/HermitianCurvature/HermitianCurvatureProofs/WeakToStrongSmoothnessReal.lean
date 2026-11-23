import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Filter Topology Set

noncomputable section

namespace Formalism.FourierDecayAlt.P.Ux11

section real

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Norming {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (lam : I → V →L[ℝ] E) : Prop :=
  ∀ (v : V) (c : ℝ), (∀ i, ‖lam i v‖ ≤ c) → ‖v‖ ≤ c

lemma Norming.nonempty {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {lam : I → V →L[ℝ] E}
    (hN : Norming lam) : Nonempty I := by
  by_contra h
  have := hN 0 (-1) (fun i => (h ⟨i⟩).elim)
  rw [norm_zero] at this
  linarith

lemma Norming.eq {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {lam : I → V →L[ℝ] E}
    (hN : Norming lam) {v w : V} (h : ∀ i, lam i v = lam i w) : v = w := by
  have := hN (v - w) 0 (fun i => by rw [map_sub, h i, sub_self, norm_zero])
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

lemma lip_ball {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → F} {x₀ : X} {r M : ℝ}
    (hd : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ f y)
    (hb : ∀ y ∈ Metric.ball x₀ r, ‖fderiv ℝ f y‖ ≤ M) {y : X} (hy : y ∈ Metric.ball x₀ r) :
    ‖f y - f x₀‖ ≤ M * ‖y - x₀‖ :=
  (convex_ball x₀ r).norm_image_sub_le_of_norm_fderiv_le hd hb
    (Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hy)) hy

lemma taylor2 {f : X → E} {x₀ : X} {r M : ℝ}
    (hd : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ f y)
    (hd2 : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ (fderiv ℝ f) y)
    (hb : ∀ y ∈ Metric.ball x₀ r, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) {h : X} (hh : ‖h‖ < r) :
    ‖f (x₀ + h) - f x₀ - fderiv ℝ f x₀ h‖ ≤ M * ‖h‖ ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg h) hh
  have hx₀ : x₀ ∈ Metric.ball x₀ r := Metric.mem_ball_self hr
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hb x₀ hx₀)
  have hsub : Metric.closedBall x₀ ‖h‖ ⊆ Metric.ball x₀ r := Metric.closedBall_subset_ball hh
  have key : ‖(f (x₀ + h) - fderiv ℝ f x₀ (x₀ + h)) - (f x₀ - fderiv ℝ f x₀ x₀)‖ ≤
      M * ‖h‖ * ‖x₀ + h - x₀‖ :=
    (convex_closedBall x₀ ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun y => f y - fderiv ℝ f x₀ y) (f' := fun y => fderiv ℝ f y - fderiv ℝ f x₀) (C := M * ‖h‖)
      (fun y hy => ((hd y (hsub hy)).hasFDerivAt.sub (fderiv ℝ f x₀).hasFDerivAt).hasFDerivWithinAt)
      (fun y hy => by
        have h1 := lip_ball hd2 hb (hsub hy)
        have h2 : ‖y - x₀‖ ≤ ‖h‖ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hy
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hM))
      (Metric.mem_closedBall_self (norm_nonneg h))
      (show x₀ + h ∈ Metric.closedBall x₀ ‖h‖ by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left])
  have e : (f (x₀ + h) - fderiv ℝ f x₀ (x₀ + h)) - (f x₀ - fderiv ℝ f x₀ x₀) =
      f (x₀ + h) - f x₀ - fderiv ℝ f x₀ h := by rw [map_add]; abel
  rw [e, add_sub_cancel_left] at key
  calc _ ≤ M * ‖h‖ * ‖h‖ := key
    _ = M * ‖h‖ ^ 2 := by ring

lemma exists_vec {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {lam : I → V →L[ℝ] E} (hN : Norming lam) {Φ : X → V} {x₀ : X} {r M : ℝ} (hr : 0 < r)
    (D : I → X →L[ℝ] E)
    (hT : ∀ i, ∀ h : X, ‖h‖ < r → ‖lam i (Φ (x₀ + h)) - lam i (Φ x₀) - D i h‖ ≤ M * ‖h‖ ^ 2)
    (h : X) : ∃ v : V, ∀ i, lam i v = D i h := by
  obtain ⟨i₀⟩ := hN.nonempty
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = r / (2 * (‖h‖ + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεh : ε * ‖h‖ < r := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg h]
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, ∀ n, t n = ε * (1 / 2) ^ n := ⟨_, fun _ => rfl⟩
  have ht0 : ∀ n, 0 < t n := fun n => by rw [ht]; positivity
  have htε : ∀ n, t n ≤ ε := fun n => by
    rw [ht]; exact mul_le_of_le_one_right hε0.le (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨q, hq⟩ : ∃ q : ℕ → V, ∀ n, q n = (t n)⁻¹ • (Φ (x₀ + t n • h) - Φ x₀) := ⟨_, fun _ => rfl⟩
  have key : ∀ i n, ‖lam i (q n) - D i h‖ ≤ M * ‖h‖ ^ 2 * t n := by
    intro i n
    have htn := (ht0 n).ne'
    have hn : ‖t n • h‖ < r := by
      rw [norm_smul, Real.norm_of_nonneg (ht0 n).le]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (htε n) (norm_nonneg h)) hεh
    have e : lam i (q n) - D i h =
        (t n)⁻¹ • (lam i (Φ (x₀ + t n • h)) - lam i (Φ x₀) - D i (t n • h)) := by
      rw [hq, map_smul, map_sub, map_smul, smul_sub, smul_sub, inv_smul_smul₀ htn, smul_sub]
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (ht0 n).le)]
    calc (t n)⁻¹ * ‖lam i (Φ (x₀ + t n • h)) - lam i (Φ x₀) - D i (t n • h)‖
        ≤ (t n)⁻¹ * (M * ‖t n • h‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hT i _ hn) (inv_nonneg.2 (ht0 n).le)
      _ = M * ‖h‖ ^ 2 * t n := by
          rw [norm_smul, Real.norm_of_nonneg (ht0 n).le]; field_simp
  have hMh : 0 ≤ M * ‖h‖ ^ 2 := by
    have := (norm_nonneg _).trans (key i₀ 0)
    nlinarith [ht0 0]
  have hdist : ∀ n, dist (q n) (q (n + 1)) ≤ (2 * (M * ‖h‖ ^ 2) * ε) * (1 / 2) ^ n := by
    intro n
    rw [dist_eq_norm]
    refine hN _ _ (fun i => ?_)
    have e : lam i (q n - q (n + 1)) = (lam i (q n) - D i h) - (lam i (q (n + 1)) - D i h) := by
      rw [map_sub]; abel
    rw [e]
    have hp : 0 ≤ ε * (1 / 2 : ℝ) ^ n := by positivity
    calc _ ≤ ‖lam i (q n) - D i h‖ + ‖lam i (q (n + 1)) - D i h‖ := norm_sub_le _ _
      _ ≤ M * ‖h‖ ^ 2 * t n + M * ‖h‖ ^ 2 * t (n + 1) := add_le_add (key i n) (key i (n + 1))
      _ ≤ _ := by
        rw [ht, ht, pow_succ (1 / 2 : ℝ) n]
        nlinarith [mul_nonneg hMh hp]
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric (1 / 2) _ (by norm_num) hdist)
  refine ⟨v, fun i => ?_⟩
  have h1 : Tendsto (fun n => lam i (q n)) atTop (𝓝 (lam i v)) := ((lam i).continuous.tendsto v).comp hv
  have h2 : Tendsto (fun n => lam i (q n)) atTop (𝓝 (D i h)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => key i n) ?_
    have : Tendsto (fun n : ℕ => M * ‖h‖ ^ 2 * (ε * (1 / 2 : ℝ) ^ n)) atTop (𝓝 (M * ‖h‖ ^ 2 * (ε * 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
    rw [mul_zero, mul_zero] at this
    simpa only [ht] using this
  exact tendsto_nhds_unique h1 h2

lemma norm_iter_comp {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : F →L[ℝ] G) {g : X → F} {Ω : Set X} {n : WithTop ℕ∞} (hg : ContDiffOn ℝ n g Ω)
    (hΩ : IsOpen Ω) {x : X} (hx : x ∈ Ω) {q : ℕ} (hq : (q : WithTop ℕ∞) ≤ n) :
    ‖iteratedFDeriv ℝ q (fun y => L (g y)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ q g x‖ := by
  rw [← iteratedFDerivWithin_of_isOpen q hΩ hx, ← iteratedFDerivWithin_of_isOpen q hΩ hx]
  exact L.norm_iteratedFDerivWithin_comp_left (hg x hx) hΩ.uniqueDiffOn hx hq

lemma iter_congr {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : X → F} {Ω : Set X}
    (hΩ : IsOpen Ω) (h : ∀ y ∈ Ω, f y = g y) {x : X} (hx : x ∈ Ω) (q : ℕ) :
    iteratedFDeriv ℝ q f x = iteratedFDeriv ℝ q g x := by
  rw [← iteratedFDerivWithin_of_isOpen q hΩ hx, ← iteratedFDerivWithin_of_isOpen q hΩ hx]
  exact iteratedFDerivWithin_congr (fun y hy => h y hy) hx q

lemma norm_apply_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (h : X) (hh : ‖h‖ ≤ 1) :
    ‖ContinuousLinearMap.apply ℝ F h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => by
    rw [ContinuousLinearMap.apply_apply, one_mul]
    exact (T.le_opNorm h).trans (mul_le_of_le_one_right (norm_nonneg _) hh))

lemma loc {Ω : Set X} {bd : X → ℝ} (hΩ : IsOpen Ω) (hbd : ContinuousOn bd Ω) {x₀ : X} (hx : x₀ ∈ Ω) :
    ∃ r > 0, ∀ y ∈ Metric.ball x₀ r, y ∈ Ω ∧ bd y ≤ bd x₀ + 1 := by
  have h2 : ∀ᶠ y in 𝓝 x₀, bd y ∈ Iic (bd x₀ + 1) :=
    Filter.Tendsto.eventually (hbd.continuousAt (hΩ.mem_nhds hx)) (Iic_mem_nhds (lt_add_one _))
  have h1 : ∀ᶠ y in 𝓝 x₀, y ∈ Ω ∧ bd y ≤ bd x₀ + 1 := Filter.Eventually.and (hΩ.mem_nhds hx) h2
  exact Metric.eventually_nhds_iff_ball.1 h1

variable [FiniteDimensional ℝ X]

lemma hasFDeriv_of {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {lam : I → V →L[ℝ] E} (hN : Norming lam) {Φ : X → V} {x₀ : X} {r M : ℝ} (hr : 0 < r)
    (D : I → X →L[ℝ] E)
    (hT : ∀ i, ∀ h : X, ‖h‖ < r → ‖lam i (Φ (x₀ + h)) - lam i (Φ x₀) - D i h‖ ≤ M * ‖h‖ ^ 2) :
    ∃ L : X →L[ℝ] V, HasFDerivAt Φ L x₀ ∧ ∀ i, (lam i).comp L = D i := by
  choose ℓ hℓ using exists_vec hN hr D hT
  let ℓ' : X →ₗ[ℝ] V :=
    { toFun := ℓ
      map_add' := fun a b => hN.eq (fun i => by rw [map_add, hℓ, hℓ, hℓ, map_add])
      map_smul' := fun c a => hN.eq (fun i => by rw [map_smul, hℓ, hℓ, map_smul]; rfl) }
  have hL : ∀ h, (LinearMap.toContinuousLinearMap ℓ') h = ℓ h := fun h => rfl
  refine ⟨LinearMap.toContinuousLinearMap ℓ', ?_, fun i => ?_⟩
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : X => ‖h‖ ^ 2) ?_
      (Asymptotics.isLittleO_norm_pow_id one_lt_two)
    refine Asymptotics.IsBigO.of_bound M ?_
    filter_upwards [Metric.ball_mem_nhds (0 : X) hr] with h hh
    rw [mem_ball_zero_iff] at hh
    rw [Real.norm_of_nonneg (by positivity)]
    refine hN _ _ (fun i => ?_)
    have e : lam i (Φ (x₀ + h) - Φ x₀ - (LinearMap.toContinuousLinearMap ℓ') h) =
        lam i (Φ (x₀ + h)) - lam i (Φ x₀) - D i h := by
      rw [map_sub, map_sub, hL, hℓ]
    rw [e]; exact hT i h hh
  · ext h; rw [ContinuousLinearMap.comp_apply, hL, hℓ]

theorem weak_to_strong_smoothness_real (m : ℕ) : ∀ (V I : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (lam : I → V →L[ℝ] E), Norming lam → ∀ (Ω : Set X) (Φ : X → V) (bd : X → ℝ), IsOpen Ω →
    ContinuousOn bd Ω →
    (∀ i, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => lam i (Φ x)) Ω) →
    (∀ i, ∀ q ≤ m + 1, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ q (fun x => lam i (Φ x)) x‖ ≤ bd x) →
    ContDiffOn ℝ (m : WithTop ℕ∞) Φ Ω ∧ ∀ q ≤ m, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ q Φ x‖ ≤ bd x := by
  induction m with
  | zero =>
    intro V I _ _ _ lam hN Ω Φ bd hΩ hbd hcd hb
    have h0 : ∀ x ∈ Ω, ‖Φ x‖ ≤ bd x := fun x hx => hN _ _ (fun i => by
      have := hb i 0 (Nat.zero_le _) x hx
      rwa [norm_iteratedFDeriv_zero] at this)
    refine ⟨?_, fun q hq x hx => ?_⟩
    · have hc : ContinuousOn Φ Ω := by
        intro x₀ hx₀
        obtain ⟨r, hr, hball⟩ := loc hΩ hbd hx₀
        refine (continuousAt_of_locally_lipschitz hr (bd x₀ + 1) (fun y hy => ?_)).continuousWithinAt
        rw [dist_eq_norm, dist_eq_norm]
        refine hN _ _ (fun i => ?_)
        rw [map_sub]
        refine lip_ball (f := fun x => lam i (Φ x)) (fun z hz => ?_) (fun z hz => ?_) hy
        · exact ((hcd i).differentiableOn (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))).differentiableAt
            (hΩ.mem_nhds (hball z hz).1)
        · rw [← norm_iteratedFDeriv_one]
          exact (hb i 1 (by omega) z (hball z hz).1).trans (hball z hz).2
      have := (contDiffOn_zero (𝕜 := ℝ)).2 hc
      simpa using this
    · obtain rfl : q = 0 := Nat.le_zero.1 hq
      rw [norm_iteratedFDeriv_zero]; exact h0 x hx
  | succ m ih =>
    intro V I _ _ _ lam hN Ω Φ bd hΩ hbd hcd hb
    obtain ⟨i₀⟩ := hN.nonempty
    have hf1 : ∀ i, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ (fun x => lam i (Φ x))) Ω :=
      fun i => (hcd i).fderiv_of_isOpen hΩ (by push_cast; exact le_rfl)
    have hdiff : ∀ i, ∀ y ∈ Ω, DifferentiableAt ℝ (fun x => lam i (Φ x)) y := fun i y hy =>
      ((hcd i).differentiableOn (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))).differentiableAt (hΩ.mem_nhds hy)
    have hdiff2 : ∀ i, ∀ y ∈ Ω, DifferentiableAt ℝ (fderiv ℝ (fun x => lam i (Φ x))) y := fun i y hy =>
      ((hf1 i).differentiableOn (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))).differentiableAt (hΩ.mem_nhds hy)
    have hder : ∀ x₀ ∈ Ω, ∃ L : X →L[ℝ] V, HasFDerivAt Φ L x₀ ∧
        ∀ i, (lam i).comp L = fderiv ℝ (fun x => lam i (Φ x)) x₀ := by
      intro x₀ hx₀
      obtain ⟨r, hr, hball⟩ := loc hΩ hbd hx₀
      refine hasFDeriv_of hN hr (M := bd x₀ + 1) _ (fun i h hh => ?_)
      have hmem : ∀ y ∈ Metric.ball x₀ r, y ∈ Ω := fun y hy => (hball y hy).1
      exact taylor2 (f := fun x => lam i (Φ x)) (fun y hy => hdiff i y (hmem y hy))
        (fun y hy => hdiff2 i y (hmem y hy))
        (fun y hy => by
          rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
          exact (hb i 2 (by omega) y (hmem y hy)).trans (hball y hy).2) hh
    have hD : ∀ x ∈ Ω, HasFDerivAt Φ (fderiv ℝ Φ x) x ∧
        ∀ i, (lam i).comp (fderiv ℝ Φ x) = fderiv ℝ (fun x => lam i (Φ x)) x := by
      intro x hx
      obtain ⟨L, hL, hc⟩ := hder x hx
      rw [hL.fderiv]; exact ⟨hL, hc⟩
    let lam' : I × {h : X // ‖h‖ ≤ 1} → (X →L[ℝ] V) →L[ℝ] E :=
      fun j => (lam j.1).comp (ContinuousLinearMap.apply ℝ V j.2.1)
    have hlam' : ∀ j T, lam' j T = lam j.1 (T j.2.1) := fun j T => rfl
    have hN' : Norming lam' := by
      intro T c hc
      have c0 : 0 ≤ c := by
        have := hc (i₀, ⟨0, by simp⟩)
        rwa [hlam', map_zero, map_zero, norm_zero] at this
      refine ContinuousLinearMap.opNorm_le_of_unit_norm c0 (fun h hh => hN _ _ (fun i => ?_))
      have := hc (i, ⟨h, hh.le⟩)
      rwa [hlam'] at this
    have heq : ∀ j : I × {h : X // ‖h‖ ≤ 1}, ∀ y ∈ Ω, lam' j (fderiv ℝ Φ y) =
        ContinuousLinearMap.apply ℝ E j.2.1 (fderiv ℝ (fun x => lam j.1 (Φ x)) y) := by
      intro j y hy
      rw [hlam', ContinuousLinearMap.apply_apply, ← (hD y hy).2 j.1]; rfl
    have hcd' : ∀ j, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => lam' j (fderiv ℝ Φ x)) Ω := by
      intro j
      exact ((ContinuousLinearMap.apply ℝ E j.2.1).contDiff.comp_contDiffOn (hf1 j.1)).congr
        (fun x hx => heq j x hx)
    have hb' : ∀ j, ∀ q ≤ m + 1, ∀ x ∈ Ω,
        ‖iteratedFDeriv ℝ q (fun x => lam' j (fderiv ℝ Φ x)) x‖ ≤ bd x := by
      intro j q hq x hx
      rw [iter_congr hΩ (heq j) hx q]
      calc _ ≤ ‖ContinuousLinearMap.apply ℝ E j.2.1‖ *
            ‖iteratedFDeriv ℝ q (fderiv ℝ (fun x => lam j.1 (Φ x))) x‖ :=
            norm_iter_comp _ (hf1 j.1) hΩ hx (by exact_mod_cast hq)
        _ ≤ 1 * bd x := by
            refine mul_le_mul (norm_apply_le _ j.2.2) ?_ (norm_nonneg _) zero_le_one
            rw [norm_iteratedFDeriv_fderiv]; exact hb j.1 (q + 1) (by omega) x hx
        _ = bd x := one_mul _
    obtain ⟨hcD, hbD⟩ := ih (X →L[ℝ] V) (I × {h : X // ‖h‖ ≤ 1}) lam' hN' Ω (fun x => fderiv ℝ Φ x) bd
      hΩ hbd hcd' hb'
    refine ⟨?_, fun q hq x hx => ?_⟩
    · rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
      refine ⟨fun x hx => (hD x hx).1.differentiableAt.differentiableWithinAt, fun h => ?_, hcD⟩
      simp at h
    · rcases q with _ | q
      · rw [norm_iteratedFDeriv_zero]
        exact hN _ _ (fun i => by
          have := hb i 0 (Nat.zero_le _) x hx
          rwa [norm_iteratedFDeriv_zero] at this)
      · rw [← norm_iteratedFDeriv_fderiv]
        exact hbD q (by omega) x hx

end real

theorem _root_.Formalism.FourierDecayAlt.P.weak_to_strong_smoothness : Formalism.FourierDecayAlt.U.WeakToStrong := by
  intro X V E I _ _ _ _ _ _ _ _ lam hN Ω Φ m bd hΩ hbd hcd hb
  exact weak_to_strong_smoothness_real (X := X) (E := E) m V I (fun i => (lam i).restrictScalars ℝ) hN Ω Φ bd hΩ hbd hcd hb

section thm

def Idx (k ρ mm : ℕ) : Type :=
  {t : List (B.Mat k ρ) × List (B.Mat k ρ) × B.Mat k ρ //
    U.unitW k ρ t.1 ∧ U.unitW k ρ t.2.1 ∧ t.1.length + t.2.1.length ≤ mm ∧ t.2.2 ∈ B.GV k ρ}

variable {k ρ mm : ℕ} {E V : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
  [NormedSpace ℂ V] {a : ℝ} {S : Set (B.Mat k ρ)}

lemma gNa_nonneg (γ : B.Mat k ρ) (a : ℝ) : 0 ≤ B.gN γ ^ a := Real.rpow_nonneg (Real.sqrt_nonneg _) a

lemma ev_add (M : U.CCModel k ρ E a mm S V) (w₁ w₂ : V) :
    M.ev (w₁ + w₂) = fun g => M.ev w₁ g + M.ev w₂ g := by
  rw [map_add]; rfl

lemma ev_smul (M : U.CCModel k ρ E a mm S V) (c : ℂ) (w : V) : M.ev (c • w) = fun g => c • M.ev w g := by
  rw [map_smul]; rfl

lemma ck_len (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) (w : V) :
    B.CkOn (((BetaSesquilinearity.wL t.1.1 ++ BetaSesquilinearity.wR t.1.2.1).length : ℕ) : ℕ∞) (B.GV k ρ) (M.ev w) :=
  BetaSesquilinearity.sCkOn_mono (by rw [BetaSesquilinearity.len_LR]; exact_mod_cast t.2.2.2.1) (M.mem w).1

def lamL (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) : V →ₗ[ℂ] E where
  toFun w := ((B.gN t.1.2.2 ^ a : ℝ) : ℂ) • B.dLR t.1.1 t.1.2.1 (M.ev w) t.1.2.2
  map_add' w₁ w₂ := by
    rw [ev_add, BetaSesquilinearity.dLR_eq, BetaSesquilinearity.Dw_add (BetaSesquilinearity.lie_LR (BetaSesquilinearity.unit_lie t.2.1) (BetaSesquilinearity.unit_lie t.2.2.1))
      (ck_len M t w₁) (ck_len M t w₂) _ t.2.2.2.2, ← BetaSesquilinearity.dLR_eq, ← BetaSesquilinearity.dLR_eq, smul_add]
  map_smul' c w := by
    simp only [ev_smul, BetaSesquilinearity.dLR_eq, BetaSesquilinearity.Dw_smul, RingHom.id_apply]
    exact smul_comm _ _ _

lemma lamL_norm (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) (w : V) : ‖lamL M t w‖ ≤ ‖w‖ := by
  show ‖((B.gN t.1.2.2 ^ a : ℝ) : ℂ) • B.dLR t.1.1 t.1.2.1 (M.ev w) t.1.2.2‖ ≤ ‖w‖
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (gNa_nonneg _ _)]
  exact (M.mem w).2 _ _ t.2.1 t.2.2.1 t.2.2.2.1 _ t.2.2.2.2

def lamC (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) : V →L[ℂ] E :=
  (lamL M t).mkContinuous 1 (fun w => by rw [one_mul]; exact lamL_norm M t w)

lemma lamC_apply (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) (w : V) :
    lamC M t w = ((B.gN t.1.2.2 ^ a : ℝ) : ℂ) • B.dLR t.1.1 t.1.2.1 (M.ev w) t.1.2.2 := rfl

lemma lamC_norming (M : U.CCModel k ρ E a mm S V) (w : V) (c : ℝ) (h : ∀ t, ‖lamC M t w‖ ≤ c) : ‖w‖ ≤ c := by
  refine M.least w c ⟨(M.mem w).1, fun u v hu hv hl g hg => ?_⟩
  have := h ⟨(u, v, g), hu, hv, hl, hg⟩
  have e : ‖lamC M ⟨(u, v, g), hu, hv, hl, hg⟩ w‖ = B.gN g ^ a * ‖B.dLR u v (M.ev w) g‖ := by
    show ‖((B.gN g ^ a : ℝ) : ℂ) • B.dLR u v (M.ev w) g‖ = _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (gNa_nonneg _ _)]
  exact (le_of_eq e.symm).trans this

def sc (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℝ) : E →L[ℝ] E :=
  ((c : ℂ) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

lemma sc_apply (c : ℝ) (y : E) : sc E c y = (c : ℂ) • y := rfl

lemma sc_norm (c : ℝ) (hc : 0 ≤ c) : ‖sc E c‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc (fun y => by
    rw [sc_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc])

end thm

theorem _root_.Formalism.FourierDecayAlt.P.theorem_u_of_parts : Formalism.FourierDecayAlt.U.TheoremUOfParts := by
  intro hU41 hSupp hW k p s ρ σ d hd hs K hK hK0 m mm Q A₁ hQ ha
  obtain ⟨C, hC⟩ := hU41 k p s ρ σ d hd hs K hK hK0 m mm Q A₁ hQ ha
  refine ⟨C, fun z z' E _ _ _ F₁ B₁ hStar => ?_⟩
  obtain ⟨hint, hcc, hder⟩ := hC z z' E F₁ B₁ hStar
  refine ⟨hint, fun Z hZ hKZ γ hγ => hSupp k p s ρ σ d z z' E F₁ A₁ B₁ Q K hd hStar Z hZ hKZ γ hγ, ?_⟩
  intro S V _ _ _ M hS
  have hex : ∀ Z : G.Mat s, ∃ v : V, G.detM Z ≠ 0 →
      ∀ γ ∈ B.GV k ρ, M.ev v γ = U.PhiFun k ρ σ d z z' F₁ Z γ := by
    intro Z
    by_cases hZ : G.detM Z ≠ 0
    · obtain ⟨v, hv⟩ := M.surj _ ⟨_, hcc Z hZ⟩ (hS Z hZ)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => absurd h hZ⟩
  choose Φ hΦ using hex
  refine ⟨Φ, hΦ, ?_⟩
  have hdet : Continuous (fun Z : G.Mat s => G.detM Z) := by
    unfold G.detM
    exact Continuous.matrix_det continuous_id
  have hΩ : IsOpen {Z : G.Mat s | G.detM Z ≠ 0} := isOpen_ne_fun hdet continuous_const
  have hbd : ContinuousOn (fun Z : G.Mat s => C * B₁ * (1 + ‖Z‖) ^ (-(U.a1 (p + s + ρ) A₁ m mm)))
      {Z : G.Mat s | G.detM Z ≠ 0} :=
    (continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
      (fun Z => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg Z)).ne'))).continuousOn
  have key : ∀ (t : Idx k ρ mm), ∀ Z ∈ {Z : G.Mat s | G.detM Z ≠ 0}, lamC M t (Φ Z) =
      sc E (B.gN t.1.2.2 ^ (U.a1 (p + s + ρ) A₁ m mm))
        (B.dLR t.1.1 t.1.2.1 (U.PhiFun k ρ σ d z z' F₁ Z) t.1.2.2) := by
    intro t Z hZ
    rw [lamC_apply, sc_apply]
    congr 1
    rw [BetaSesquilinearity.dLR_eq, BetaSesquilinearity.dLR_eq]
    exact BetaSesquilinearity.Dw_congr (BetaSesquilinearity.lie_LR (BetaSesquilinearity.unit_lie t.2.1) (BetaSesquilinearity.unit_lie t.2.2.1)) (hΦ Z hZ) _ t.2.2.2.2
  obtain ⟨hcont, hbound⟩ := hW (G.Mat s) V E (Idx k ρ mm) (lamC M) (lamC_norming M)
    {Z : G.Mat s | G.detM Z ≠ 0} Φ m (fun Z => C * B₁ * (1 + ‖Z‖) ^ (-(U.a1 (p + s + ρ) A₁ m mm)))
    hΩ hbd
    (fun t => ((sc E _).contDiff.comp_contDiffOn
      (hder t.1.1 t.1.2.1 t.2.1 t.2.2.1 t.2.2.2.1 t.1.2.2 t.2.2.2.2).1).congr (fun Z hZ => key t Z hZ))
    (fun t q hq Z hZ => by
      rw [iter_congr hΩ (key t) hZ q]
      have h2 := (hder t.1.1 t.1.2.1 t.2.1 t.2.2.1 t.2.2.2.1 t.1.2.2 t.2.2.2.2).2 q hq Z hZ
      calc _ ≤ ‖sc E (B.gN t.1.2.2 ^ (U.a1 (p + s + ρ) A₁ m mm))‖ *
            ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s =>
              B.dLR t.1.1 t.1.2.1 (U.PhiFun k ρ σ d z z' F₁ Z') t.1.2.2) Z‖ :=
            norm_iter_comp _ (hder t.1.1 t.1.2.1 t.2.1 t.2.2.1 t.2.2.2.1 t.1.2.2 t.2.2.2.2).1 hΩ hZ
              (by exact_mod_cast hq)
        _ ≤ B.gN t.1.2.2 ^ (U.a1 (p + s + ρ) A₁ m mm) *
            ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s =>
              B.dLR t.1.1 t.1.2.1 (U.PhiFun k ρ σ d z z' F₁ Z') t.1.2.2) Z‖ :=
            mul_le_mul_of_nonneg_right (sc_norm _ (gNa_nonneg _ _)) (norm_nonneg _)
        _ ≤ _ := h2)
  exact fun Z hZ => ⟨hcont.contDiffAt (hΩ.mem_nhds hZ), fun q hq => hbound q hq Z hZ⟩

end Formalism.FourierDecayAlt.P.Ux11
