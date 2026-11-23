import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdaptC
import Development.WeilBound.ThetaLifts.LeviDeterminants.NormIteratedFDerivIdLeOneAdd

noncomputable section

open scoped SchwartzMap

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt Lib

variable {A κ κ₀ κ₁ : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [Fintype κ] [Fintype κ₀] [Fintype κ₁] (ε : κ ≃ κ₀ ⊕ κ₁)

theorem hcongr {f g : ℝ → ℂ} {a b : ℂ} {x : ℝ} (h : HasDerivAt f a x) (hf : ∀ t, g t = f t) (ha : b = a) : HasDerivAt g b x := by
  rw [ha, funext hf]; exact h

theorem hd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ)) (x v : V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f (x + s • v) v) s := by
  have h := (f.hasFDerivAt (x + s • v)).comp_hasDerivAt s (((hasDerivAt_id s).smul_const v).const_add x)
  rw [one_smul] at h
  exact h

theorem hd0 {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ)) (x v : V) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  simpa using hd f x v 0

theorem dop_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) (c : ℂ) (f : 𝓢(V, ℂ)) :
    dop a L (c • f) = c • dop a L f := by
  ext x
  have h1 := op_apply a L (c • f) x
  have h2 := op_apply a L f x
  rw [LineDeriv.lineDerivOp_smul] at h1
  change op a L (c • f) x = c * op a L f x
  rw [h1, h2]
  change c * _ + _ * (_ * (c * _)) = _
  ring

theorem dop_add' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) (f g : 𝓢(V, ℂ)) :
    dop a L (f + g) = dop a L f + dop a L g := by
  simp only [dop, LineDeriv.lineDerivOp_add, map_add, smul_add]
  abel

theorem dop_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    dop (-a) (-L) f = -dop a L f := by
  ext x
  simp only [SchwartzMap.neg_apply, dop_apply, map_neg, ContinuousLinearMap.neg_apply]
  push_cast
  ring

omit [Fintype κ₀] in
theorem slice_dop (f : 𝓢(κ → A, ℂ)) (g : 𝓢(κ₁ → A, ℂ)) (a : κ₀ → A) (h : ∀ y, g y = f (glue ε a y)) (L : (κ → A) →L[ℝ] ℝ)
    (L₁ : (κ₁ → A) →L[ℝ] ℝ) (hL : ∀ y, L (glue ε a y) = L₁ y) (v y : κ₁ → A) :
    dop (glue ε 0 v) L f (glue ε a y) = dop v L₁ g y := by
  rw [dop_apply, dop_apply, hL, h]
  congr 1
  refine (hd0 f _ _).unique ?_
  refine hcongr (hd0 g y v) (fun t => ?_) rfl
  rw [h, glue_smul, glue_add, smul_zero, add_zero]

omit [Fintype κ₀] [Fintype κ₁] in
theorem slice_normal (f : 𝓢(κ → A, ℂ)) (h : (κ₁ → A) → ℂ) (hf : ∀ a, ∃ c : ℂ, ∀ y, f (glue ε a y) = c * h y) (p a : κ₀ → A) :
    ∃ c : ℂ, ∀ y, fderiv ℝ f (glue ε a y) (glue ε p 0) = c * h y := by
  have e : ∀ y (t : ℝ), glue ε a y + t • glue ε p 0 = glue ε (a + t • p) y := fun y t => by
    rw [glue_smul, glue_add, smul_zero, add_zero]
  by_cases h0 : h = 0
  · refine ⟨0, fun y => (hd0 f _ _).unique ?_⟩
    refine hcongr (hasDerivAt_const (0 : ℝ) (0 : ℂ)) (fun t => ?_) ?_
    · obtain ⟨c, hc⟩ := hf (a + t • p)
      rw [e, hc, h0]; simp
    · simp
  · obtain ⟨y₀, hy⟩ := Function.ne_iff.1 h0
    refine ⟨fderiv ℝ f (glue ε a y₀) (glue ε p 0) / h y₀, fun y => (hd0 f _ _).unique ?_⟩
    refine hcongr (((hd0 f (glue ε a y₀) (glue ε p 0)).div_const (h y₀)).mul_const (h y)) (fun t => ?_) rfl
    obtain ⟨c, hc⟩ := hf (a + t • p)
    rw [e, e, hc, hc, mul_div_cancel_right₀ _ hy]

omit [Fintype κ₀] [Fintype κ₁] in
theorem slice_ode (f : 𝓢(κ → A, ℂ)) (a : κ₀ → A) (l : ℝ)
    (h : ∀ (t : ℝ) y, fderiv ℝ f (glue ε (t • a) y) (glue ε a 0) = -(2 * t * l) * f (glue ε (t • a) y)) (y : κ₁ → A) :
    f (glue ε a y) = Complex.exp (-l) * f (glue ε 0 y) := by
  have e : ∀ t : ℝ, glue ε 0 y + t • glue ε a 0 = glue ε (t • a) y := fun t => by
    rw [glue_smul, glue_add, smul_zero, add_zero, zero_add]
  have h1 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) ^ 2 * l) * f (glue ε 0 y + t • glue ε a 0)) 0 s := fun s => by
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * l) (2 * s * l) s := by
      simpa using (((hasDerivAt_pow 2 (s : ℂ)).comp_ofReal).mul_const (l : ℂ))
    refine hcongr (h2.cexp.fun_mul (hd f (glue ε 0 y) (glue ε a 0) s)) (fun _ => rfl) ?_
    rw [e, h]
    ring
  have h3 := is_const_of_deriv_eq_zero (fun s => (h1 s).differentiableAt) (fun s => (h1 s).deriv) 1 0
  simp only [e] at h3
  simp only [one_smul, zero_smul, Complex.ofReal_one, one_pow, one_mul, Complex.ofReal_zero] at h3
  rw [Complex.exp_neg, eq_inv_mul_iff_mul_eq₀ (Complex.exp_ne_zero _), h3]
  simp

theorem exists_gauss_box [FiniteDimensional ℝ A] (Q : (κ₀ → A) →ₗ[ℝ] (κ₀ → A) →ₗ[ℝ] ℝ) (hs : ∀ a b, Q a b = Q b a)
    (hp : ∀ a, a ≠ 0 → 0 < Q a a) (g : 𝓢(κ₁ → A, ℂ)) : ∃ f : 𝓢(κ → A, ℂ), (∀ y, f (glue ε 0 y) = g y) ∧
      (∀ a, ∃ c : ℂ, ∀ y, f (glue ε a y) = c * g y) ∧
      ∀ a y p, fderiv ℝ f (glue ε a y) (glue ε p 0) = -(2 * Real.pi * Q a p) * f (glue ε a y) := by
  let Qc : (κ₀ → A) →L[ℝ] (κ₀ → A) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((κ₀ → A) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ ((-Real.pi) • Q))
  have hQ : ∀ a b, Qc a b = -Real.pi * Q a b := fun _ _ => rfl
  obtain ⟨G, hG⟩ := exists_schwartz_exp_diag Qc fun a ha => by
    rw [hQ]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (hp a ha)
  let f := schwartzBox G g (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε.symm (.inl i)))
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε.symm (.inr i))) fun x : κ → A => by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      obtain ⟨k, rfl⟩ := ε.symm.surjective k
      rcases k with k | k
      · exact le_max_of_le_left (norm_le_pi_norm (fun i => x (ε.symm (.inl i))) k)
      · exact le_max_of_le_right (norm_le_pi_norm (fun i => x (ε.symm (.inr i))) k)
  have hf : ∀ a y, f (glue ε a y) = Complex.exp (-Real.pi * Q a a) * g y := fun a y => by
    show G (fun i => glue ε a y _) * g (fun i => glue ε a y _) = _
    simp only [glue_inl, glue_inr, hG, hQ]
    push_cast
    rfl
  refine ⟨f, fun y => by simp [hf], fun a => ⟨_, hf a⟩, fun a y p => (hd0 f _ _).unique ?_⟩
  have h2 : HasDerivAt (fun t : ℝ => -(Real.pi : ℂ) * (Q a a + 2 * t * Q a p + (t : ℂ) ^ 2 * Q p p))
      (-(Real.pi : ℂ) * (2 * (Q a p : ℂ))) 0 :=
    hcongr ((((((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul 2).mul_const (Q a p : ℂ)).const_add (Q a a : ℂ)).fun_add
      ((hasDerivAt_pow 2 ((0 : ℝ) : ℂ)).mul_const (Q p p : ℂ))).const_mul (-(Real.pi : ℂ))).comp_ofReal (fun _ => rfl) (by simp)
  refine hcongr (h2.cexp.mul_const (g y)) (fun t => ?_) ?_
  · skip
    rw [glue_smul, glue_add, smul_zero, add_zero, hf]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hs p a]
    push_cast
    congr 2
    ring
  · rw [hf]
    simp
    ring

end PositivityTheory.ThKF0
