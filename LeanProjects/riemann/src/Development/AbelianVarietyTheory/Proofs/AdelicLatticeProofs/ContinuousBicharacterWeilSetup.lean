import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExpSeriesContDiffAndHasDerivAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CharSeriesExistsNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SummableGaussianCoset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPosMulNormSqLe
open scoped ContDiff

namespace GlobalTheory.HeisenbergGaussianSeries

theorem exists_coercive {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ om v (J v) := by
  first
  | exact @_root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le
  | exact _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le
  | (apply _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le ..)

theorem exists_exponent {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) :
    ∃ M : V →L[ℝ] V →L[ℝ] ℂ, ∀ y v, M y v =
      -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)) := by
  let m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun y v => -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)))
    (by intro a b v; simp; ring) (by intro a b v; simp; ring)
    (by intro a b v; simp; ring) (by intro a b v; simp; ring)
  exact ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℂ)).toLinearMap ∘ₗ m),
    fun y v => rfl⟩

theorem contDiff_bilin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) :
    ContDiff ℝ ∞ fun v : V => om v (J v) := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ)).toLinearMap ∘ₗ om)
  have h1 : ContDiff ℝ ∞ fun v : V => B v (LinearMap.toContinuousLinearMap J v) :=
    B.contDiff.clm_apply (LinearMap.toContinuousLinearMap J).contDiff
  exact h1

theorem swap_mul {G : Type} [AddCommGroup G] (β : G → G → ℂ)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (x y : G) : β x y * β y x = 1 := by
  have := hd (x + y)
  rw [hl, hr, hr, hd, hd] at this
  simpa using this

theorem summable_coeff {G V : Type} [AddCommGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (p : G →+ V) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (Γ U₀ : AddSubgroup G) (χ : G → ℂ) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v))
    (hinj : ∀ g ∈ Γ, p g = 0 → g = 0)
    (hfin : ∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite)
    (hχ0 : ∀ x, x ∉ U₀ → χ x = 0) (hχ1 : ∀ x, ‖χ x‖ ≤ 1)
    (b : Γ → ℂ) (hb : ∀ g, ‖b g‖ = 1) (w : G) (y : V) (M : V →L[ℝ] V →L[ℝ] ℂ) (R : ℝ) :
    Summable fun g : Γ => ‖b g * χ (g + w) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ))‖ *
        Real.exp (R * ‖M (p g + y)‖) := by
  obtain ⟨c, hc, hq⟩ := exists_coercive om J hpos
  have hs := GlobalTheory.GaussCoset.summable_gaussian_coset G V p Γ U₀ hinj hfin (Real.pi / 2 * c) (by positivity) (|R| * ‖M‖) w y
  refine Summable.of_nonneg_of_le (fun g => by positivity) (fun g => ?_) hs
  by_cases hg : (g : G) + w ∈ U₀
  · rw [Set.indicator_of_mem (by exact hg), norm_mul, norm_mul, hb, one_mul, Complex.norm_exp,
      Real.exp_add]
    have h1 : (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ)).re
        = -(Real.pi / 2) * om (p g + y) (J (p g + y)) := by
      have : (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ))
        = ((-(Real.pi / 2) * om (p g + y) (J (p g + y)) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_re]
    rw [h1]
    have h2 : -(Real.pi / 2) * om (p g + y) (J (p g + y))
        ≤ -(Real.pi / 2 * c) * ‖p g + y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left (hq (p g + y)) (show 0 ≤ Real.pi / 2 by positivity)
      linarith
    have h3 : R * ‖M (p g + y)‖ ≤ |R| * ‖M‖ * ‖p g + y‖ := by
      rw [mul_assoc]
      exact mul_le_mul (le_abs_self R) (M.le_opNorm _) (norm_nonneg _) (abs_nonneg _)
    refine mul_le_mul ?_ (Real.exp_le_exp.mpr h3) (by positivity) (by positivity)
    exact (mul_le_of_le_one_left (by positivity) (hχ1 _)).trans (Real.exp_le_exp.mpr h2)
  · rw [Set.indicator_of_notMem (by exact hg), hχ0 _ hg]
    simp

noncomputable def series {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (Γ : AddSubgroup G) (χ : G → ℂ) (a : V) (w : G) : ℂ :=
  ∑' g : Γ, β g w * β (ι a) (g + w) * χ (g + w) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))

section
variable {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    {p : G →+ V} {ι : V →+ G} {β : G → G → ℂ} {om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {J : V →ₗ[ℝ] V}
    {Γ : AddSubgroup G} {χ : G → ℂ}

theorem series_quasi
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hΓ : ∀ g ∈ Γ, ∀ g' ∈ Γ, β g g' = 1) (a : V) (g₀ : G) (hg₀ : g₀ ∈ Γ) (w : G) :
    β g₀ w * series p ι β om J Γ χ a (g₀ + w) = series p ι β om J Γ χ a w := by
  unfold series
  rw [← tsum_mul_left]
  refine Eq.trans ?_ ((Equiv.addRight (⟨g₀, hg₀⟩ : Γ)).tsum_eq _)
  refine tsum_congr fun g => ?_
  have e1 : p g + (a + p (g₀ + w)) = p (g + g₀) + (a + p w) := by simp only [map_add]; abel
  simp only [Equiv.coe_addRight, AddSubgroup.coe_add]
  rw [e1, hr g g₀ w, hΓ g g.2 g₀ hg₀, hl g g₀ w, add_assoc (g : G) g₀ w]
  ring

theorem series_inv
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (a : V) (u : G) (hu : p u = 0) (hχ : ∀ x, β x u * χ (x + u) = χ x) (w : G) :
    β w u * series p ι β om J Γ χ a (w + u) = series p ι β om J Γ χ a w := by
  unfold series
  rw [← tsum_mul_left]
  refine tsum_congr fun g => ?_
  have h1 : β (ι a) u = 1 := by
    have := swap_mul β hl hr hd (ι a) u
    rw [hβ u a, hu] at this
    simpa using this
  rw [← hχ (g + w), ← add_assoc (g : G) w u, hr (ι a) (g + w) u, h1, hr g w u, hl g w u,
    map_add p w u, hu,
    add_zero]
  ring

theorem series_expand (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (hsym : ∀ x y, om x (J y) = om y (J x)) (hχ : ∀ x v, χ (x + ι v) = χ x)
    (M : V → V → ℂ)
    (hM : ∀ y v, M y v = -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)))
    (a : V) (w : G) (v : V) :
    β w (ι v) * series p ι β om J Γ χ a (w + ι v) =
      Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) *
      ∑' g : Γ, (β g w * β (ι a) (g + w) * χ (g + w) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
        Complex.exp (M (p g + (a + p w)) v) := by
  unfold series
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun g => ?_
  have e1 : p g + (a + p (w + ι v)) = (p g + (a + p w)) + v := by rw [map_add, hp]; abel
  have e2 : β w (ι v) * β g (ι v) * β (ι a) (ι v) =
      Complex.exp (-(Real.pi * Complex.I) * (om (p g + (a + p w)) v : ℝ)) := by
    rw [← hl, ← hl, hβ, map_add p, map_add p, hp]
    congr 5; abel
  rw [e1, ← add_assoc (g : G) w, hχ, hr (ι a) (g + w), hr g w, hM]
  set y := p g + (a + p w)
  have e3 : Complex.exp (-(Real.pi * Complex.I) * (om y v : ℝ)) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (y + v) (J (y + v)) : ℝ)) =
      Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om y (J y) : ℝ)) *
      Complex.exp (-(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add, LinearMap.add_apply, hsym v y]
    push_cast; ring
  linear_combination (β g w * β (ι a) (g + w) * χ (g + w) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (y + v) (J (y + v)) : ℝ))) * e2 +
    (β g w * β (ι a) (g + w) * χ (g + w)) * e3

theorem series_neg (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (halt : ∀ v, om v v = 0) (hχ : ∀ x v, χ (x + ι v) = χ x) (a : V) :
    series p ι β om J Γ χ a (ι (-a)) =
      ∑' g : Γ, (χ g * Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g) (J (p g)) : ℝ))) *
        Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)) := by
  unfold series
  refine tsum_congr fun g => ?_
  have h1 : β (ι a) g = Complex.exp (Real.pi * Complex.I * (om (p g) a : ℝ)) := by
    have := swap_mul β hl hr hd (ι a) g
    rw [hβ g a] at this
    rw [eq_inv_of_mul_eq_one_left this, ← Complex.exp_neg]
    congr 1; ring
  have h2 : Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)) =
      Complex.exp (Real.pi * Complex.I * (om (p g) a : ℝ)) *
      Complex.exp (Real.pi * Complex.I * (om (p g) a : ℝ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hχ, hr, h1, h2, hβ, hβ, hp, hp, add_neg_cancel, add_zero]
  simp [halt]
  ring
end

theorem exists_theta : ∀ (G V : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (Γ U₀ U : AddSubgroup G) (χ : G → ℂ), Continuous p → Continuous ι → (∀ v, p (ι v) = v) → (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ x y, ‖β x y‖ = 1) → Continuous (fun q : G × G => β q.1 q.2) → (∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ))) → (∀ v, om v v = 0) → (∀ v, J (J v) = -v) → (∀ x y, om x (J y) = om y (J x)) → (∀ v, v ≠ 0 → 0 < om v (J v)) → (∀ g ∈ Γ, ∀ g' ∈ Γ, β g g' = 1) → (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ v, ι v ∈ U₀) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite) → (∀ x, x ∉ U₀ → χ x = 0) → (∀ x, ‖χ x‖ ≤ 1) → χ 0 = 1 → (∀ x v, χ (x + ι v) = χ x) → IsOpen (U : Set G) → (∀ u ∈ U, ∀ x, β x (u - ι (p u)) * χ (x + (u - ι (p u))) = χ x) → ∃ f : G → ℂ, f ≠ 0 ∧ Continuous f ∧ (∀ g ∈ Γ, ∀ w, β g w * f (g + w) = f w) ∧ (∀ u, p u = 0 → (∀ x, β x u * χ (x + u) = χ x) → ∀ w, β w u * f (w + u) = f w) ∧ (∀ w, ContDiff ℝ ∞ fun v : V => f (w + ι v)) ∧ ∀ w z, deriv (fun t : ℝ => β w (ι (t • z)) * f (w + ι (t • z))) 0 + Complex.I * deriv (fun t : ℝ => β w (ι (t • J z)) * f (w + ι (t • J z))) 0 = 0 := by
  intro G V _ _ _ _ _ _ p ι β om J Γ U₀ U χ hpc hιc hp hl hr hd hn hβc hβ halt hJ hsym hpos hΓ hinj
    _ hfin hχ0 hχ1 hχz hχι hU hUinv
  obtain ⟨M, hM⟩ := exists_exponent om J

  obtain ⟨a, ha⟩ : ∃ a : V, series p ι β om J Γ χ a (ι (-a)) ≠ 0 := by
    have hs := summable_coeff p om J Γ U₀ χ hpos hinj hfin hχ0 hχ1 (fun _ => 1) (by simp) 0 0 M 0
    simp only [one_mul, add_zero, zero_mul, Real.exp_zero, mul_one] at hs
    obtain ⟨a, ha⟩ := GlobalTheory.charSeries_exists_ne_zero V Γ
      (fun g a => Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)))
      (fun g => χ g * Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g) (J (p g)) : ℝ))) 0
      (fun g a b => by rw [← Complex.exp_add]; congr 1; simp only [map_add]; push_cast; ring)
      (fun g a => by
        have : (2 * Real.pi * Complex.I * (om (p g) a : ℝ) : ℂ)
          = ((2 * Real.pi * om (p g) a : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I])
      (fun a => by simp)
      (fun g hg => by
        have h1 : p g ≠ 0 := fun h => hg (Subtype.ext (hinj g g.2 h))
        have h2 := (hpos _ h1).ne'
        refine ⟨(2 * om (p g) (J (p g)))⁻¹ • J (p g), ?_⟩
        have h3 : om (p g) ((2 * om (p g) (J (p g)))⁻¹ • J (p g)) = 1 / 2 := by
          rw [map_smul, smul_eq_mul]; field_simp
        simp only [h3]
        rw [← Complex.exp_pi_mul_I]
        congr 1; push_cast; ring)
      hs (by simp [hχz])
    exact ⟨a, by rw [series_neg hp hl hr hd hβ halt hχι]; exact ha⟩
  have hexp := fun w : G => GlobalTheory.expSeries_contDiff_and_hasDerivAt V Γ
    (fun g => β g w * β (ι a) (g + w) * χ (g + w) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ)))
    (fun g => M (p g + (a + p w)))
    (summable_coeff p om J Γ U₀ χ hpos hinj hfin hχ0 hχ1 (fun g => β g w * β (ι a) (g + w))
      (fun g => by rw [norm_mul, hn, hn, one_mul]) w (a + p w) M)
  have hexpand := series_expand (Γ := Γ) hp hl hr hβ hsym hχι (fun y v => M y v) hM a
  have hne : ∀ x y, β x y ≠ 0 := fun x y h => by simpa [h] using hn x y
  have hgauss : ContDiff ℝ ∞ fun v : V => Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_bilin om J))).cexp
  have hsmooth : ∀ w, ContDiff ℝ ∞ fun v : V => series p ι β om J Γ χ a (w + ι v) := by
    intro w
    have h1 : ContDiff ℝ ∞ fun v : V => Complex.exp (Real.pi * Complex.I * (om (p w) v : ℝ)) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (LinearMap.toContinuousLinearMap (om (p w))).contDiff)).cexp
    have h2 := h1.mul (hgauss.mul (hexp w).1)
    refine (congrArg (ContDiff ℝ ∞) (funext fun v => ?_)).mp h2
    rw [← hexpand w v, hβ, ← mul_assoc, ← Complex.exp_add]
    simp
  refine ⟨series p ι β om J Γ χ a, fun h => ha (by rw [h]; rfl), ?_,
    fun g hg w => series_quasi hl hr hΓ a g hg w,
    fun u hu hχ w => series_inv hl hr hd hβ a u hu hχ w, hsmooth, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro w
    have hc1 : Continuous fun x : G => p (x - w) := hpc.comp (continuous_id.sub continuous_const)
    have hc2 : Continuous fun x : G => β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))) :=
      hβc.comp (f := fun x : G => (w + ι (p (x - w)), (x - w) - ι (p (x - w))))
        ((continuous_const.add (hιc.comp hc1)).prodMk
          ((continuous_id.sub continuous_const).sub (hιc.comp hc1)))
    have hc3 : Continuous fun x : G => (β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))))⁻¹ *
        series p ι β om J Γ χ a (w + ι (p (x - w))) :=
      (hc2.inv₀ fun x => hne _ _).mul ((hsmooth w).continuous.comp hc1)
    refine hc3.continuousAt.congr ?_
    have hnhds : ∀ᶠ x in nhds w, x - w ∈ U := by
      have : IsOpen {x : G | x - w ∈ U} := hU.preimage (continuous_id.sub continuous_const)
      exact this.mem_nhds (by simp)
    filter_upwards [hnhds] with x hx
    have h := series_inv (Γ := Γ) (J := J) hl hr hd hβ a ((x - w) - ι (p (x - w)))
      (by rw [map_sub p, hp, sub_self]) (hUinv _ hx) (w + ι (p (x - w)))
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (hne _ _), one_mul]
    congr 1; abel
  · intro w z
    have hder : ∀ z : V, HasDerivAt
        (fun t : ℝ => β w (ι (t • z)) * series p ι β om J Γ χ a (w + ι (t • z)))
        (∑' g : Γ, (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          M (p g + (a + p w)) z) 0 := by
      intro z
      have g1 : HasDerivAt (fun t : ℝ =>
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (t • z) (J (t • z)) : ℝ))) 0 0 := by
        have g0 : HasDerivAt (fun t : ℝ => om (t • z) (J (t • z))) 0 0 := by
          have := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (om z (J z))
          refine (this.congr_deriv (by simp)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun t => ?_)
          simp [mul_assoc]
        exact (g0.ofReal_comp.const_mul (-(Real.pi / 2 : ℂ))).cexp.congr_deriv (by simp)
      have g2 := g1.mul ((hexp w).2 z).2
      simp only [hexpand]
      exact g2.congr_deriv (by simp)
    rw [(hder z).deriv, (hder (J z)).deriv, ← tsum_mul_left,
      ← ((hexp w).2 z).1.tsum_add (((hexp w).2 (J z)).1.mul_left Complex.I)]
    refine (tsum_congr fun g => ?_).trans tsum_zero
    rw [hM, hM, hJ, map_neg]
    push_cast
    linear_combination (-(Real.pi : ℂ) * (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          (om (p g + (a + p w)) (J z) : ℝ)) * Complex.I_mul_I

end GlobalTheory.HeisenbergGaussianSeries
