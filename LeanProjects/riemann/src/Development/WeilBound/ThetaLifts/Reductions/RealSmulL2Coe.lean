import Mathlib
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieF
import Development.WeilBound.ThetaLifts.Reductions.MetaDef

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff

namespace PositivityTheory.ThKR

open GlobalTheory.RealWeil PositivityTheory.RL.Up

section Tele

variable {𝕜 V B : Type} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V] [NormedAddCommGroup B] [NormedSpace 𝕜 B]

theorem tele (j : V →ₗ[𝕜] B) (L : V →ₗ[𝕜] V) (μ : 𝕜) {q : ℝ} (hq : 1 ≤ q) (hL : ∀ v, ‖j (L v)‖ ≤ q * ‖j v‖)
    (hμ : ‖μ‖ ≤ q) (f : V) (n : ℕ) : ‖j (L^[n] f) - μ ^ n • j f‖ ≤ n * q ^ n * ‖j (L f) - μ • j f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : j (L^[n + 1] f) - μ ^ (n + 1) • j f = j (L (L^[n] f - μ ^ n • f)) + μ ^ n • (j (L f) - μ • j f) := by
      rw [Function.iterate_succ_apply']
      simp only [map_sub, map_smul, smul_sub, smul_smul, pow_succ]
      abel
    have h1 := hL (L^[n] f - μ ^ n • f)
    rw [map_sub j, map_smul j] at h1
    have h2 : ‖μ ^ n • (j (L f) - μ • j f)‖ ≤ q ^ n * ‖j (L f) - μ • j f‖ := by
      rw [norm_smul, norm_pow]
      gcongr
    have hq0 : 0 ≤ q := by linarith
    have h3 : q ^ n * ‖j (L f) - μ • j f‖ ≤ q * (q ^ n * ‖j (L f) - μ • j f‖) :=
      le_mul_of_one_le_left (by positivity) hq
    have h4 := mul_le_mul_of_nonneg_left ih hq0
    rw [e]
    refine (norm_add_le _ _).trans ?_
    push_cast
    rw [pow_succ]
    nlinarith

theorem tele_lim (j : V →ₗ[𝕜] B) (L : ℝ → V →ₗ[𝕜] V) (μ : ℝ → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), (∀ v, ‖j (L t v)‖ ≤ (1 + C * |t|) * ‖j v‖) ∧ ‖μ t‖ ≤ 1 + C * |t|) (f : V)
    (ho : (fun t => j (L t f) - μ t • j f) =o[𝓝 0] fun t => t) :
    Tendsto (fun n : ℕ => j ((L (n : ℝ)⁻¹)^[n] f) - μ (n : ℝ)⁻¹ ^ n • j f) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have h1 := (ho.norm_left.tendsto_div_nhds_zero.comp hi).const_mul (Real.exp C)
  rw [mul_zero] at h1
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [hi.eventually h, eventually_gt_atTop 0] with n hn hn0
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn0
  have ha : |(n : ℝ)⁻¹| = (n : ℝ)⁻¹ := abs_of_pos (inv_pos.2 hn1)
  refine (tele j _ _ (le_add_of_nonneg_right (by positivity)) hn.1 hn.2 f n).trans ?_
  have h2 : (1 + C * |(n : ℝ)⁻¹|) ^ n ≤ Real.exp C := by
    calc _ ≤ Real.exp (C * (n : ℝ)⁻¹) ^ n := by
          rw [ha]
          gcongr
          rw [add_comm]
          exact Real.add_one_le_exp _
      _ = _ := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  simp only [Function.comp_apply, div_inv_eq_mul]
  calc _ ≤ n * Real.exp C * ‖j (L (n : ℝ)⁻¹ f) - μ (n : ℝ)⁻¹ • j f‖ := by gcongr
    _ = _ := by ring

end Tele

theorem norm_le_lin {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] {g : ℝ → B} {g' : B} (h : HasDerivAt g g' 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0 : ℝ), ‖g t - g 0‖ ≤ C * |t| := by
  obtain ⟨C, hC, h⟩ := h.isBigO_sub.exists_nonneg
  refine ⟨C, hC, h.bound.mono fun t ht => ?_⟩
  simpa using ht

theorem pow_lim {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (k : ℝ → 𝔸) (h0 : k 0 = 1) (hd : HasDerivAt k 0 0) :
    Tendsto (fun n : ℕ => k (n : ℝ)⁻¹ ^ n) atTop (𝓝 1) := by
  obtain ⟨C, hC, h⟩ := norm_le_lin hd
  have := tele_lim (𝕜 := ℝ) LinearMap.id (fun t => LinearMap.mulLeft ℝ (k t)) (fun _ => 1) hC
    (h.mono fun t ht => ⟨fun v => ?_, ?_⟩) 1 (by simpa [h0] using hasDerivAt_iff_isLittleO_nhds_zero.1 hd)
  · rw [← tendsto_sub_nhds_zero_iff]
    refine this.congr fun n => ?_
    have e : (LinearMap.mulLeft ℝ (k (n : ℝ)⁻¹))^[n] 1 = k (n : ℝ)⁻¹ ^ n := mul_left_iterate_apply_one _
    simp [e]
  · show ‖k t * v‖ ≤ _ * ‖v‖
    have e : k t * v = v + (k t - k 0) * v := by rw [h0, sub_mul, one_mul, add_sub_cancel]
    rw [e, add_mul, one_mul]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((norm_mul_le _ _).trans (by gcongr)))
  · have : 0 ≤ C * |t| := by positivity
    simpa using this

variable {l : Type} [Fintype l]

theorem real_smul_L2_coe (t : ℝ) (v : L2 l) : (t : ℂ) • v = t • v := algebraMap_smul ℂ t v

theorem j_ne {f : Sch l} (hf : f ≠ 0) : schwartzToL2 l f ≠ 0 := fun h =>
  hf (SchwartzMap.injective_toLp (E := EuclideanSpace ℝ l) (F := ℂ) 2 volume (h.trans (map_zero (schwartzToL2 l)).symm))

def Conf (U : Sch l →L[ℂ] Sch l) : Prop := ∃ n : ℝ, ∀ f, ‖schwartzToL2 l (U f)‖ = n * ‖schwartzToL2 l f‖

theorem delta_zero {G : Type} [Group G] [TopologicalSpace G] (A : G →* (Sch l →L[ℂ] Sch l))
    (hw : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun g => T (A g f)) (hc : ∀ g, Conf (A g)) (k : ℝ → G) (k0 : k 0 = 1)
    (hk : Tendsto (fun n : ℕ => k (n : ℝ)⁻¹ ^ n) atTop (𝓝 1)) (d : ℂ)
    (hd : ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (k t) f)) (d • schwartzToL2 l f) 0) : cexp d = 1 := by
  obtain ⟨f, hf⟩ := exists_ne (l := l)
  have hj := j_ne hf
  have hp : 0 < ‖schwartzToL2 l f‖ := norm_pos_iff.2 hj
  have he : HasDerivAt (fun t : ℝ => cexp (d * t)) d 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul d).cexp
  obtain ⟨C1, hC1, h1⟩ := norm_le_lin (hd f)
  obtain ⟨C2, hC2, h2⟩ := norm_le_lin he
  have h3 := tele_lim (C := C1 / ‖schwartzToL2 l f‖ + C2) (schwartzToL2 l).toLinearMap (fun t => (A (k t)).toLinearMap)
    (fun t => cexp (d * t)) (by positivity) ?_ f ?_
  · let T : L2 l →L[ℂ] ℂ := innerSL ℂ (schwartzToL2 l f)
    have h4 := (T.continuous.tendsto _).comp h3
    have h5 := ((hw (T ∘L schwartzToL2 l) f).tendsto 1).comp hk
    have h6 : Tendsto (fun n : ℕ => cexp d * T (schwartzToL2 l f)) atTop (𝓝 (T (schwartzToL2 l f))) := by
      have := h5.sub h4
      simp only [map_one, map_zero, sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have e : cexp (d * ((n : ℝ)⁻¹ : ℝ)) ^ n = cexp d := by
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        field_simp
      have e' : ∀ U : Sch l →L[ℂ] Sch l, (U ^ n) f = U^[n] f := fun U => congrFun (hom_coe_pow _ rfl (fun _ _ => rfl) U n) f
      simp only [Function.comp_apply, e, map_pow, ContinuousLinearMap.comp_apply, e',
        ContinuousLinearMap.coe_coe, map_sub, map_smul, smul_eq_mul]
      ring
    have h7 := tendsto_nhds_unique tendsto_const_nhds h6
    have h8 : T (schwartzToL2 l f) ≠ 0 := fun h => hj (inner_self_eq_zero.1 h)
    exact mul_right_cancel₀ h8 (h7.trans (one_mul _).symm)
  · filter_upwards [h1, h2] with t a1 a2
    simp only [k0, map_one, ContinuousLinearMap.one_apply, ofReal_zero, mul_zero, Complex.exp_zero] at a1 a2
    refine ⟨fun v => ?_, ?_⟩
    · obtain ⟨n, hn⟩ := hc (k t)
      show ‖schwartzToL2 l (A (k t) v)‖ ≤ _ * ‖schwartzToL2 l v‖
      rw [hn]
      gcongr
      have b1 := norm_le_norm_add_norm_sub' (schwartzToL2 l (A (k t) f)) (schwartzToL2 l f)
      rw [hn] at b1
      have b2 : n ≤ 1 + C1 / ‖schwartzToL2 l f‖ * |t| := by
        refine le_of_mul_le_mul_right ?_ hp
        rw [add_mul, mul_right_comm, div_mul_cancel₀ _ hp.ne']
        linarith
      have : 0 ≤ C2 * |t| := by positivity
      linarith
    · have b1 := norm_le_norm_add_norm_sub' (cexp (d * t)) 1
      have : 0 ≤ C1 / ‖schwartzToL2 l f‖ * |t| := by positivity
      rw [norm_one] at b1
      linarith
  · have := hasDerivAt_iff_isLittleO_nhds_zero.1 ((hd f).sub (he.smul_const (schwartzToL2 l f)))
    simpa [k0] using this

theorem bd_of_conf (U : ℝ → Sch l →L[ℂ] Sch l) (hc : ∀ t, Conf (U t))
    (hw : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun t => T (U t f)) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ f, ‖schwartzToL2 l (U t f)‖ ≤ C * ‖schwartzToL2 l f‖ := by
  obtain ⟨f, hf⟩ := exists_ne (l := l)
  have hp : 0 < ‖schwartzToL2 l f‖ := norm_pos_iff.2 (j_ne hf)
  obtain ⟨M, hM⟩ := bdd_of_weak (fun t => schwartzToL2 l (U t f)) fun φ => hw (φ ∘L schwartzToL2 l) f
  refine ⟨M / ‖schwartzToL2 l f‖, fun t ht g => ?_⟩
  obtain ⟨n, hn⟩ := hc t
  have := hM t ht
  rw [hn] at this ⊢
  gcongr
  rwa [le_div_iff₀ hp]

theorem exists_avg (S : ℝ → Sch l →L[ℂ] Sch l) (hc : ∀ t, Conf (S t)) (S0 : S 0 = 1) (Sm : ∀ t u, S (t + u) = S t * S u)
    (Sc : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun t => T (S t f)) {φ : Sch l} (hφ : φ ≠ 0) :
    ∃ mu : Sch l →L[ℂ] ℂ, mu φ ≠ 0 ∧ DifferentiableAt ℝ (fun t => mu (S t φ)) 0 := by
  let lam : Sch l →L[ℂ] ℂ := (innerSL ℂ (schwartzToL2 l φ)).comp (schwartzToL2 l)
  have h2 : lam φ ≠ 0 := fun h => j_ne hφ (inner_self_eq_zero.1 h)
  obtain ⟨C, hC⟩ := bd_of_conf S hc Sc
  have hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ f, ‖lam (S t f)‖ ≤ ‖schwartzToL2 l φ‖ * (C * ‖schwartzToL2 l f‖) := fun t ht f =>
    (norm_inner_le_norm (𝕜 := ℂ) (schwartzToL2 l φ) (schwartzToL2 l (S t f))).trans
      (mul_le_mul_of_nonneg_left (hC t ht f) (norm_nonneg _))
  have hc := Sc lam φ
  have hI : ∀ t, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, lam (S s φ)) (lam (S t φ)) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _)
      hc.continuousAt
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ ∈ Set.Icc (-1 : ℝ) 1, (∫ s in (0 : ℝ)..δ, lam (S s φ)) ≠ 0 := by
    by_contra h
    push Not at h
    have h3 := hI 0
    simp only [S0, ContinuousLinearMap.one_apply] at h3
    refine h2 (h3.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq ?_))
    filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht using h t ht
  let m : Sch l →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ s in (0 : ℝ)..δ, lam (S s f)
      map_add' := fun f g => by
        simp only [map_add]
        exact intervalIntegral.integral_add ((Sc lam f).intervalIntegrable _ _) ((Sc lam g).intervalIntegrable _ _)
      map_smul' := fun a f => by
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul _ _ }
  have mc : Continuous m := by
    refine continuous_of_continuousAt_zero m ?_
    rw [ContinuousAt, map_zero]
    have h0 : Continuous fun f : Sch l => ‖schwartzToL2 l φ‖ * (C * ‖schwartzToL2 l f‖) * |δ - 0| := by fun_prop
    have h1 := h0.tendsto 0
    simp only [map_zero, norm_zero, mul_zero, zero_mul] at h1
    exact squeeze_zero_norm (fun f => intervalIntegral.norm_integral_le_of_norm_le_const fun s hs =>
      hb s (Set.uIcc_subset_Icc (by norm_num) hδ1 (Set.uIoc_subset_uIcc hs)) f) h1
  refine ⟨⟨m, mc⟩, hδ, ?_⟩
  have key : ∀ t, m (S t φ) = (∫ s in (0 : ℝ)..(δ + t), lam (S s φ)) - ∫ s in (0 : ℝ)..t, lam (S s φ) := fun t => by
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have := intervalIntegral.integral_comp_add_right (fun s => lam (S s φ)) (a := 0) (b := δ) t
    rw [zero_add] at this
    rw [← this]
    simp only [Sm]
    rfl
  show DifferentiableAt ℝ (fun t => m (S t φ)) 0
  simp only [key]
  exact (((hI (δ + 0)).comp_const_add δ 0).sub (hI 0)).differentiableAt

theorem strong (S : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l →L[ℂ] Sch l) (S0 : S 0 = 1) (Sm : ∀ t u, S (t + u) = S t * S u)
    (h : ∀ (T : Sch l →L[ℂ] ℂ) f, HasDerivAt (fun t => T (S t f)) (T (Q f)) 0) (f : Sch l) :
    HasDerivAt (fun t => schwartzToL2 l (S t f)) (schwartzToL2 l (Q f)) 0 := by
  have hd : ∀ (T : Sch l →L[ℂ] ℂ) g s, HasDerivAt (fun t => T (S t g)) (T (S s (Q g))) s := fun T g s => by
    have a := h (T ∘L S s) g
    rw [← sub_self s] at a
    refine (a.comp_sub_const s s).congr_of_eventuallyEq (.of_forall fun t => ?_)
    show _ = T ((S s * S (t - s)) g)
    rw [← Sm, add_sub_cancel]
  obtain ⟨M, hM⟩ := bdd_of_weak (fun t => schwartzToL2 l (S t (Q (Q f)))) fun φ =>
    continuous_iff_continuousAt.2 fun s => (hd (φ ∘L schwartzToL2 l) _ s).continuousAt
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num))
  have key : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ‖schwartzToL2 l (S t f) - schwartzToL2 l f - (t : ℂ) • schwartzToL2 l (Q f)‖ ≤ M * t ^ 2 := fun t ht => by
    refine NormedSpace.norm_le_dual_bound ℂ _ (by positivity) fun φ => ?_
    have := taylor2 _ _ _ (hd (φ ∘L schwartzToL2 l) f) (hd (φ ∘L schwartzToL2 l) (Q f)) (M := ‖φ‖ * M) (fun v hv =>
      (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM v hv) (norm_nonneg _))) ht
    simp only [S0, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply] at this
    simp only [map_sub, map_smul, smul_eq_mul]
    linarith
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (g := fun t : ℝ => t ^ 2) (IsBigO.of_bound M ?_) (isLittleO_pow_id (by norm_num))
  filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht
  have := key t ht
  rw [real_smul_L2_coe] at this
  simpa [S0] using this

theorem dif_mul {U U' : ℝ → Sch l →L[ℂ] Sch l} {Q Q' : Sch l →L[ℂ] Sch l} (U0 : U 0 = 1) (U0' : U' 0 = 1) {C : ℝ}
    (hC : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ f, ‖schwartzToL2 l (U t f)‖ ≤ C * ‖schwartzToL2 l f‖)
    (h : ∀ f, HasDerivAt (fun t => schwartzToL2 l (U t f)) (schwartzToL2 l (Q f)) 0)
    (h' : ∀ f, HasDerivAt (fun t => schwartzToL2 l (U' t f)) (schwartzToL2 l (Q' f)) 0) (f : Sch l) :
    HasDerivAt (fun t => schwartzToL2 l ((U t * U' t) f)) (schwartzToL2 l ((Q + Q') f)) 0 := by
  have a1 : HasDerivAt (fun t : ℝ => schwartzToL2 l (U t (U' t f - f - (t : ℂ) • Q' f))) 0 0 := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 (h' f)
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    refine IsBigO.trans_isLittleO (IsBigO.of_bound C ?_) this
    filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht
    have := hC t ht (U' t f - f - (t : ℂ) • Q' f)
    rw [map_sub (schwartzToL2 l), map_sub (schwartzToL2 l), map_smul (schwartzToL2 l), real_smul_L2_coe] at this
    simp only [zero_add, U0', ContinuousLinearMap.one_apply, ofReal_zero, zero_smul, sub_self, map_zero, smul_zero,
      sub_zero]
    exact this
  have a2 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).smul (h (Q' f))
  refine (((a1.add (h f)).add a2).congr_deriv (by simp [U0])).congr_of_eventuallyEq (.of_forall fun t => ?_)
  simp only [Pi.add_apply, Pi.smul_apply', id, map_sub, map_smul, ContinuousLinearMap.mul_apply]
  abel

variable [DecidableEq l]

def Im (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (U : Sch l →L[ℂ] Sch l) : Prop :=
  (∀ f, ‖schwartzToL2 l (U f)‖ = ‖schwartzToL2 l f‖) ∧ ∀ w f, U (rhoS w f) = rhoS (s *ᵥ w) (U f)

theorem Im.of_impl {s : Matrix (l ⊕ l) (l ⊕ l) ℝ} {U : Sch l →L[ℂ] Sch l}
    (h : PositivityTheory.ThKF.E.Impl (fun w => s *ᵥ w) U.toLinearMap) : Im s U :=
  ⟨h.norm, fun w f => SchwartzMap.ext fun x =>
    (congrFun (h.impl w f (rhoS w f) (funext (rhoS_apply w f))) x).trans (rhoS_apply _ _ _).symm⟩

theorem Im.one : Im (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) 1 := ⟨fun _ => rfl, fun w f => by rw [one_mulVec]; rfl⟩

theorem Im.mul {s s' : Matrix (l ⊕ l) (l ⊕ l) ℝ} {U U' : Sch l →L[ℂ] Sch l} (h : Im s U) (h' : Im s' U') :
    Im (s * s') (U * U') :=
  ⟨fun f => (h.1 _).trans (h'.1 f), fun w f => by
    rw [ContinuousLinearMap.mul_apply, h'.2, h.2, mulVec_mulVec]
    rfl⟩

theorem Im.inv {s s' : Matrix (l ⊕ l) (l ⊕ l) ℝ} {U : (Sch l →L[ℂ] Sch l)ˣ} (h : Im s U.1) (hs : s * s' = 1) :
    Im s' U⁻¹.1 := by
  have e : ∀ f, U.1 (U⁻¹.1 f) = f := fun f => by rw [← ContinuousLinearMap.mul_apply, Units.mul_inv]; rfl
  have e' : ∀ f, U⁻¹.1 (U.1 f) = f := fun f => by rw [← ContinuousLinearMap.mul_apply, Units.inv_mul]; rfl
  refine ⟨fun f => by rw [← h.1, e], fun w f => ?_⟩
  have := h.2 (s' *ᵥ w) (U⁻¹.1 f)
  rw [mulVec_mulVec, hs, one_mulVec, e] at this
  rw [← this, e']

theorem Im.covD {s : Matrix (l ⊕ l) (l ⊕ l) ℝ} {U : Sch l →L[ℂ] Sch l} (h : Im s U) (w : l ⊕ l → ℝ) :
    U * dRho w = dRho (s *ᵥ w) * U := by
  ext f x
  let T : Sch l →L[ℂ] ℂ := BoundedContinuousFunction.evalCLM ℂ x ∘L toBoundedContinuousFunctionCLM ℂ _ ℂ
  have h1 := hasDerivAt_rhoS w f (T ∘L U)
  have h2 := hasDerivAt_rhoS (s *ᵥ w) (U f) T
  simp only [ContinuousLinearMap.comp_apply, h.2, mulVec_smul] at h1
  exact h1.unique h2

theorem Im.quad {s : Matrix (l ⊕ l) (l ⊕ l) ℝ} {U : Sch l →L[ℂ] Sch l} (h : Im s U)
    (hs : ∀ w w', sympl (s *ᵥ w) (s *ᵥ w') = sympl w w') {s' : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hs' : s * s' = 1)
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : U * quad X = quad (s * X * s') * U := by
  let u : l ⊕ l → l ⊕ l → ℝ := fun b => (X * Matrix.J l ℝ) *ᵥ Pi.single b 1
  have h1 : ∀ w, X *ᵥ w = ∑ b, sympl (Pi.single b 1) w • u b := fun w => by
    have e : X *ᵥ w = (X * Matrix.J l ℝ) *ᵥ (-(Matrix.J l ℝ *ᵥ w)) := by
      rw [mulVec_neg, mulVec_mulVec, Matrix.mul_assoc, Matrix.J_squared, Matrix.mul_neg, Matrix.mul_one, neg_mulVec, neg_neg]
    rw [e, ← Finset.univ_sum_single (-(Matrix.J l ℝ *ᵥ w)), mulVec_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sympl_single, ← mulVec_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rfl
  have h2 : ∀ w, (s * X * s') *ᵥ w = ∑ b, sympl (s *ᵥ Pi.single b 1) w • s *ᵥ u b := fun w => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, h1, mulVec_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mulVec_smul, ← hs, mulVec_mulVec w, hs', one_mulVec]
  rw [quad_eq X _ _ h1, quad_eq _ _ _ h2, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun b _ => ?_)
  have e : ∀ a b, U * (dRho a * dRho b) = dRho (s *ᵥ a) * dRho (s *ᵥ b) * U := fun a b => by
    rw [← mul_assoc, h.covD, mul_assoc, h.covD, mul_assoc]
  rw [mul_add, add_mul, e, e]

theorem quad_add (X Y : Matrix (l ⊕ l) (l ⊕ l) ℝ) : quad (X + Y) = quad X + quad Y := by
  simp only [quad, Matrix.add_mul, Matrix.add_apply, add_div, ofReal_add, add_smul, Finset.sum_add_distrib, smul_add]
  abel

theorem quad_smul (r : ℝ) (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : quad (r • X) = (r : ℂ) • quad X := by
  simp only [quad, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_div_assoc, ofReal_mul, mul_smul,
    ← Finset.smul_sum]
  exact smul_comm _ _ _

theorem exists_im (hL : LocalLift) {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (t : ℝ) :
    ∃ U : (Sch l →L[ℂ] Sch l)ˣ, Im (NormedSpace.exp (t • X)) U.1 := by
  obtain ⟨ε, V, W, -, hε, -, hV, -⟩ := hL l X hX
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / ε)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  obtain ⟨h1, h2, h3⟩ := hV (t / n) (by
    rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hε] at hn
    linarith)
  let U : (Sch l →L[ℂ] Sch l)ˣ := ⟨V (t / n), W (t / n), ContinuousLinearMap.ext h1, ContinuousLinearMap.ext h2⟩
  have hp : ∀ m : ℕ, Im (NormedSpace.exp ((t / n) • X) ^ m) (U ^ m).1 := fun m => by
    induction m with
    | zero => simpa using Im.one
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul (Im.of_impl h3)
  refine ⟨U ^ n, ?_⟩
  have := hp n
  rwa [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_div_cancel₀ _ hn0.ne'] at this

theorem line (hL : LocalLift) {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ)
    (S : ℝ → Sch l →L[ℂ] Sch l) (hc : ∀ t, Conf (S t)) (S0 : S 0 = 1) (Sm : ∀ t u, S (t + u) = S t * S u)
    (Sc : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun t => T (S t f))
    (hS : ∀ (t : ℝ) (U : (Sch l →L[ℂ] Sch l)ˣ), Im (NormedSpace.exp (t • X)) U.1 → ∃ c : ℂ, S t = c • U.1) :
    ∃ z : ℂ, ∀ (T : Sch l →L[ℂ] ℂ) f, HasDerivAt (fun t => T (S t f)) (T (quad X f + z • f)) 0 := by
  obtain ⟨ε, V, W, a, hε, V0, Vi, -, Vd⟩ := hL l X hX
  obtain ⟨φ, hφ⟩ := exists_ne (l := l)
  obtain ⟨mu, hmu, md⟩ := exists_avg S hc S0 Sm Sc hφ
  have hV0 : mu (V 0 φ) ≠ 0 := by rwa [V0]
  let c : ℝ → ℂ := fun t => mu (S t φ) / mu (V t φ)
  have cd : DifferentiableAt ℝ c 0 := md.div (Vd φ mu).differentiableAt hV0
  have c0 : c 0 = 1 := by simp only [c, S0, V0]; exact div_self hmu
  have ev : ∀ᶠ t in 𝓝 (0 : ℝ), S t = c t • V t := by
    have e1 : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < ε := continuous_abs.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    filter_upwards [e1, (Vd φ mu).continuousAt.eventually_ne hV0] with t ht hne
    obtain ⟨h1, h2, h3⟩ := Vi t ht
    obtain ⟨b, hb⟩ := hS t ⟨V t, W t, ContinuousLinearMap.ext h1, ContinuousLinearMap.ext h2⟩ (Im.of_impl h3)
    have : c t = b := by
      simp only [c, hb, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
      exact mul_div_cancel_right₀ _ hne
    rw [this, hb]
  refine ⟨deriv c 0 + a, fun T f => ?_⟩
  refine ((cd.hasDerivAt.fun_mul (Vd f T)).congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp [c0, V0]
    ring
  · filter_upwards [ev] with t ht
    rw [ht, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]

end PositivityTheory.ThKR

end
