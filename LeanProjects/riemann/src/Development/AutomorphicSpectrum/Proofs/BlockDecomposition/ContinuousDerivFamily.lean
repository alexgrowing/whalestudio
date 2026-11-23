import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.LocFinType
import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont

noncomputable section

namespace GlobalTheory.CompanionTheory.WeakHolo

open Metric Set Filter Topology Complex Real

theorem taylor_two {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {s₀ : ℂ} {r M : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ (3 * r) ⊆ U) (hM : ∀ z ∈ closedBall s₀ (3 * r), ‖f z‖ ≤ M) {η : ℂ}
    (hη : ‖η‖ ≤ r) : ‖f (s₀ + η) - f s₀ - η * deriv f s₀‖ ≤ M / r ^ 2 * ‖η‖ ^ 2 := by
  have hdf : DifferentiableOn ℂ (deriv f) U :=
    ((hf.analyticOnNhd hU).deriv_of_isOpen hU).differentiableOn
  have h1 : ∀ z ∈ closedBall s₀ (2 * r), ‖deriv f z‖ ≤ M / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (3 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr (hf.diffContOnCl_ball (hsub.trans hb))
      fun w hw => hM w (hsub (sphere_subset_closedBall hw))
  have h2 : ∀ z ∈ closedBall s₀ r, ‖deriv (deriv f) z‖ ≤ M / r / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (2 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    have hsub' : closedBall s₀ (2 * r) ⊆ closedBall s₀ (3 * r) :=
      closedBall_subset_closedBall (by linarith)
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hdf.diffContOnCl_ball ((hsub.trans hsub').trans hb))
      fun w hw => h1 w (hsub (sphere_subset_closedBall hw))
  have hin : ∀ z ∈ closedBall s₀ r, z ∈ U := fun z hz =>
    hb (closedBall_subset_closedBall (by linarith) hz)
  have hc : s₀ ∈ closedBall s₀ r := mem_closedBall_self hr.le
  have h3 : ∀ z ∈ closedBall s₀ r, ‖deriv f z - deriv f s₀‖ ≤ M / r / r * ‖z - s₀‖ := fun z hz =>
    (convex_closedBall s₀ r).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (hdf y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))) h2 hc hz
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM s₀ (mem_closedBall_self (by positivity)))
  have hs : closedBall s₀ ‖η‖ ⊆ closedBall s₀ r := closedBall_subset_closedBall hη
  have h4 := (convex_closedBall s₀ ‖η‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => f z - z * deriv f s₀) (f' := fun z => deriv f z - deriv f s₀) (C := M / r / r * ‖η‖)
    (fun z hz => by
      have a := ((hf z (hin z (hs hz))).differentiableAt (hU.mem_nhds (hin z (hs hz)))).hasDerivAt
      have b := (hasDerivAt_id z).mul_const (deriv f s₀)
      have c : HasDerivAt (fun z => f z - z * deriv f s₀) (deriv f z - 1 * deriv f s₀) z := a.sub b
      rw [one_mul] at c
      exact c.hasDerivWithinAt)
    (fun z hz => (h3 z (hs hz)).trans (by
      have := mem_closedBall_iff_norm.1 hz
      gcongr))
    (mem_closedBall_self (norm_nonneg η)) (x := s₀) (y := s₀ + η) (by simp [mem_closedBall_iff_norm])
  have e : f (s₀ + η) - f s₀ - η * deriv f s₀ =
      (f (s₀ + η) - (s₀ + η) * deriv f s₀) - (f s₀ - s₀ * deriv f s₀) := by ring
  rw [e]
  refine h4.trans (le_of_eq ?_)
  simp only [add_sub_cancel_left]
  field_simp

theorem deriv_circle {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball c r)) :
    deriv f c = (2 * π * I)⁻¹ * ∮ z in C(c, r), (1 / (z - c) ^ 2) • f z := by
  have := hf.circleIntegral_one_div_sub_center_pow_smul hr 1
  simp only [zero_add, Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_one] at this
  rw [this, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by simp [pi_ne_zero]), one_mul]

theorem continuous_deriv_family {X : Type*} [TopologicalSpace X] {w : ℂ → X → ℂ} {S : Set ℂ} {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ r ⊆ S) (hd : ∀ x, DifferentiableOn ℂ (fun s => w s x) S)
    (hc : ContinuousOn (fun y : ℂ × X => w y.1 y.2) (S ×ˢ Set.univ)) :
    Continuous fun x => deriv (fun s => w s x) s₀ := by
  have e : (fun x => deriv (fun s => w s x) s₀) = fun x => (2 * π * I : ℂ)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap s₀ r) θ •
        ((1 / (circleMap s₀ r θ - s₀) ^ 2) • w (circleMap s₀ r θ) x) := by
    funext x
    rw [deriv_circle hr ((hd x).diffContOnCl_ball hb)]
    rfl
  rw [e]
  refine continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _)
  have hA : Continuous fun θ : ℝ => deriv (circleMap s₀ r) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hB : Continuous fun θ : ℝ => (1 / (circleMap s₀ r θ - s₀) ^ 2 : ℂ) :=
    continuous_const.div (((continuous_circleMap s₀ r).sub continuous_const).pow 2) fun θ =>
      pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hr.ne'))
  have hC : Continuous fun p : X × ℝ => w (circleMap s₀ r p.2) p.1 :=
    hc.comp_continuous (((continuous_circleMap s₀ r).comp continuous_snd).prodMk continuous_fst)
      fun p => ⟨hb (circleMap_mem_closedBall s₀ hr.le p.2), mem_univ _⟩
  exact (hA.comp continuous_snd).smul ((hB.comp continuous_snd).smul hC)

theorem form_scale {X : Type*} {V : Submodule ℂ (X → ℂ)} (μ : V →ₗ[ℂ] ℂ) {b : X → ℝ} {K : ℝ}
    (hK : ∀ f : V, (∀ x, ‖f.1 x‖ ≤ b x) → ‖μ f‖ ≤ K) (f : V) {l : ℝ} (hl : 0 < l)
    (hf : ∀ x, ‖f.1 x‖ ≤ l * b x) : ‖μ f‖ ≤ K * l := by
  have h := hK (((l⁻¹ : ℝ) : ℂ) • f) fun x => by
    have e : ‖(((l⁻¹ : ℝ) : ℂ) • f).1 x‖ = l⁻¹ * ‖f.1 x‖ := by
      simp [abs_of_pos hl]
    rw [e, inv_mul_le_iff₀ hl]
    exact hf x
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl),
    inv_mul_le_iff₀ hl] at h
  linarith

theorem differentiableOn_form {X : Type*} [TopologicalSpace X] {h : X → ℝ} (hh : ∀ x, 0 ≤ h x)
    {V : Submodule ℂ (X → ℂ)}
    (hV : ∀ (g : X → ℂ) (A : ℝ) (N : ℕ), Continuous g → (∀ x, ‖g x‖ ≤ A * h x ^ N) → g ∈ V)
    (μ : V →ₗ[ℂ] ℂ) (hμ : ∀ N : ℕ, ∃ C : ℝ, ∀ f : V, (∀ x, ‖f.1 x‖ ≤ h x ^ N) → ‖μ f‖ ≤ C)
    (v : ℂ → V) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × X => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * h x ^ N) :
    DifferentiableOn ℂ (fun s => μ (v s)) S := by
  intro s₀ hs₀
  obtain ⟨R, hR, hRS⟩ := nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hs₀)
  obtain ⟨C, N, hCN⟩ := hb _ hRS (isCompact_closedBall s₀ R)
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ R = 3 * r := ⟨R / 3, by positivity, by ring⟩
  have hsub : closedBall s₀ r ⊆ closedBall s₀ (3 * r) := closedBall_subset_closedBall (by linarith)
  let d : X → ℂ := fun x => deriv (fun s => (v s).1 x) s₀
  have dc : Continuous d := continuous_deriv_family (w := fun s => (v s).1) hr (hsub.trans hRS) hd hc
  have dB : ∀ x, ‖d x‖ ≤ C / r * h x ^ N := fun x => by
    have := norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun s => (v s).1 x) (c := s₀) hr
      ((hd x).diffContOnCl_ball (hsub.trans hRS)) (C := C * h x ^ N)
      fun z hz => hCN z (hsub (sphere_subset_closedBall hz)) x
    calc ‖d x‖ ≤ C * h x ^ N / r := this
      _ = C / r * h x ^ N := by ring
  let D : V := ⟨d, hV d _ N dc dB⟩
  obtain ⟨K, hK⟩ := hμ N
  set B : ℝ := |C| / r ^ 2 + 1 with hB
  have hBpos : 0 < B := by positivity
  have key : ∀ η : ℂ, ‖η‖ < r →
      ‖μ (v (s₀ + η)) - μ (v s₀) - η • μ D‖ ≤ K * B * ‖η ^ 2‖ := by
    intro η hη
    by_cases h0 : η = 0
    · simp [h0]
    have hηp : 0 < ‖η‖ := norm_pos_iff.2 h0
    have e : μ (v (s₀ + η)) - μ (v s₀) - η • μ D = μ (v (s₀ + η) - v s₀ - η • D) := by
      simp only [map_sub, map_smul]
    rw [e, norm_pow, mul_assoc]
    refine form_scale μ hK _ (by positivity) fun x => ?_
    have t := taylor_two hS (hd x) hr hRS (fun z hz => hCN z hz x) hη.le
    have hp : 0 ≤ h x ^ N := pow_nonneg (hh x) N
    have e2 : (v (s₀ + η) - v s₀ - η • D).1 x =
        (v (s₀ + η)).1 x - (v s₀).1 x - η * deriv (fun s => (v s).1 x) s₀ := rfl
    rw [e2]
    refine t.trans ?_
    have : C * h x ^ N / r ^ 2 * ‖η‖ ^ 2 = (C / r ^ 2) * (‖η‖ ^ 2 * h x ^ N) := by ring
    rw [this, show B * ‖η‖ ^ 2 * h x ^ N = B * (‖η‖ ^ 2 * h x ^ N) by ring]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hB]
    have : C / r ^ 2 ≤ |C| / r ^ 2 := by gcongr; exact le_abs_self C
    linarith
  have hO : (fun η : ℂ => μ (v (s₀ + η)) - μ (v s₀) - η • μ D) =O[𝓝 0] fun η => η ^ 2 :=
    Asymptotics.IsBigO.of_bound (K * B) (Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) hr)
      fun η hη => key η (by simpa using hη))
  exact (hasDerivAt_iff_isLittleO_nhds_zero.2
    (hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two))).differentiableAt.differentiableWithinAt

end GlobalTheory.CompanionTheory.WeakHolo

namespace GlobalTheory.CompanionTheory.WeakHolo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem mem_modFun {g : G2 σ Y → ℂ} {A : ℝ} {N : ℕ} (hg : Continuous g)
    (hA : ∀ x, ‖g x‖ ≤ A * (ht2 x : ℝ) ^ N) : g ∈ modFun σ Y := by
  have hp : 0 < |A| + 1 := by positivity
  have hq : (((|A| + 1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : ((((|A| + 1 : ℝ)) : ℂ)⁻¹ • g) ∈ modFun σ Y := by
    refine Submodule.subset_span ⟨hg.const_smul _, N, fun x => ?_⟩
    have hh : 0 ≤ (ht2 x : ℝ) ^ N := by positivity
    rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
      inv_mul_le_iff₀ hp]
    refine (hA x).trans (mul_le_mul_of_nonneg_right ?_ hh)
    linarith [le_abs_self A]
  have := (modFun σ Y).smul_mem (((|A| + 1 : ℝ)) : ℂ) h1
  rwa [smul_inv_smul₀ hq] at this

theorem wholo_growForms (v : ℂ → modFun σ Y) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × G2 σ Y => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * (ht2 x : ℝ) ^ N) :
    WHolo {μ | IsGrowForm μ} v S := fun μ hμ =>
  differentiableOn_form (h := fun x : G2 σ Y => (ht2 x : ℝ)) (fun x => NNReal.coe_nonneg _)
    (fun _ _ _ hg hA => mem_modFun hg hA) μ hμ v hS hd hc hb

end GlobalTheory.CompanionTheory.WeakHolo

end
