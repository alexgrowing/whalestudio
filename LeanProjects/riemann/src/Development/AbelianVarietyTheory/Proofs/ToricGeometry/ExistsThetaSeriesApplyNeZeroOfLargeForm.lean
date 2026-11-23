import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Complex Matrix Filter Topology
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.ThetaLarge

section General

variable {E : Type*} [NormedAddCommGroup E]

theorem exists_tsum_gauss_lt_one [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [DecidableEq L] :
    ∃ a : ℝ, 0 < a ∧ ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) < 1 := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (a : ℝ) (l : L) => if l = 0 then (0 : ℝ) else Real.exp (-a * ‖(l : E)‖ ^ 2))
    (g := fun _ => 0) (summable_lattice_exp_neg_mul_norm_sq L one_pos) (fun l => ?_) ?_
  · rw [tsum_zero] at h
    obtain ⟨a, h1, h2⟩ :=
      ((eventually_gt_atTop (0 : ℝ)).and (h.eventually (gt_mem_nhds one_pos))).exists
    exact ⟨a, h1, h2⟩
  · by_cases hl : l = 0
    · simp [hl]
    · simp only [hl, if_false]
      have hn : 0 < ‖(l : E)‖ ^ 2 := pow_pos (norm_pos_iff.2 (by simpa using hl)) 2
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.atBot_mul_const hn)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha l
    split_ifs
    · simpa using (Real.exp_pos _).le
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
      nlinarith [sq_nonneg ‖(l : E)‖]

def term (L : Submodule ℤ E) (H : E → E → ℂ) (χ : L → ℂ) (z₀ : E) (l : L) (z : E) : ℂ :=
  (χ l)⁻¹ * cexp (Real.pi * H (z + l) z₀ - (Real.pi * H z l + Real.pi / 2 * H l l))

variable {L : Submodule ℤ E} {H : E → E → ℂ} {χ : L → ℂ}

theorem term_add (hl : ∀ x y w, H (x + y) w = H x w + H y w)
    (hr : ∀ x y w, H w (x + y) = H w x + H w y) (hs : ∀ x y, H y x = (starRingEnd ℂ) (H x y))
    (h1 : ∀ l, ‖χ l‖ = 1)
    (hχ : ∀ l m : L, χ (l + m) = χ l * χ m * cexp (Real.pi * I * (H l m).im))
    (z₀ : E) (l m : L) (z : E) :
    term L H χ z₀ m (z + l) =
      (χ l * cexp (Real.pi * H z l + Real.pi / 2 * H l l)) * term L H χ z₀ (l + m) z := by
  have hne : ∀ l, χ l ≠ 0 := fun l h => by simpa [h] using h1 l
  unfold term
  rw [hχ, mul_inv, mul_inv, ← Complex.exp_neg, Submodule.coe_add, ← add_assoc]
  have e : (Real.pi * H (z + l + m) z₀ - (Real.pi * H (z + l) m + Real.pi / 2 * H m m) : ℂ) =
      (Real.pi * H z l + Real.pi / 2 * H l l) + (-(Real.pi * I * (H l m).im)) +
      (Real.pi * H (z + l + m) z₀ -
        (Real.pi * H z (l + m) + Real.pi / 2 * H (l + m) (l + m))) := by
    rw [hl z l m, hr, hl l m, hr, hr, hs l m]
    have := Complex.sub_conj (H l m)
    push_cast at this
    linear_combination (-(Real.pi : ℂ) / 2) * this
  rw [e, Complex.exp_add, Complex.exp_add]
  have := hne l
  field_simp

theorem norm_term (hl : ∀ x y w, H (x + y) w = H x w + H y w)
    (hr : ∀ x y w, H w (x + y) = H w x + H w y) (hs : ∀ x y, H y x = (starRingEnd ℂ) (H x y))
    (h1 : ∀ l, ‖χ l‖ = 1) (z₀ : E) (l : L) (z : E) :
    ‖term L H χ z₀ l z‖ = Real.exp (π / 2 * ((H z z).re + (H z₀ z₀).re)) *
      Real.exp (-(π / 2) * (H (l + (z - z₀)) (l + (z - z₀))).re) := by
  unfold term
  rw [norm_mul, norm_inv, h1, inv_one, one_mul, Complex.norm_exp, ← Real.exp_add]
  congr 1
  obtain ⟨u, rfl⟩ : ∃ u, z = u + z₀ := ⟨z - z₀, by simp⟩
  rw [add_sub_cancel_right]
  have hs' : ∀ x y, (H y x).re = (H x y).re := fun x y => by rw [hs]; simp
  have e : (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  simp only [e, hl, hr, add_re, sub_re, re_ofReal_mul]
  rw [hs' u z₀, hs' u l, hs' z₀ l]
  ring

theorem exists_theta [NormedSpace ℂ E] [FiniteDimensional ℂ E] [DiscreteTopology L]
    [DecidableEq L] (hl : ∀ x y w, H (x + y) w = H x w + H y w)
    (hr : ∀ x y w, H w (x + y) = H w x + H w y) (hs : ∀ x y, H y x = (starRingEnd ℂ) (H x y))
    (hd : ∀ w, Differentiable ℂ fun z => H z w) (hc : Continuous fun z => (H z z).re)
    {a : ℝ} (ha : 0 < a) (hsum : ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) < 1)
    (hH : ∀ z, a * ‖z‖ ^ 2 ≤ π / 2 * (H z z).re) (h1 : ∀ l, ‖χ l‖ = 1)
    (hχ : ∀ l m : L, χ (l + m) = χ l * χ m * cexp (Real.pi * I * (H l m).im)) (z₀ : E) :
    ∃ θ : E → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : L) z,
      θ (z + l) = (χ l * cexp (Real.pi * H z l + Real.pi / 2 * H l l)) * θ z := by
  have hle : ∀ (l : L) z, ‖term L H χ z₀ l z‖ ≤ Real.exp (π / 2 * ((H z z).re + (H z₀ z₀).re)) *
      Real.exp (-a * ‖(l : E) + (z - z₀)‖ ^ 2) := fun l z => by
    rw [norm_term hl hr hs h1]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    linarith [hH (l + (z - z₀))]
  refine ⟨fun z => ∑' l : L, term L H χ z₀ l z, ?_, ?_, fun l z => ?_⟩
  · rw [← differentiableOn_univ]
    refine SCV.differentiableOn_tsum_of_locally_normal isOpen_univ (fun l => ?_) (fun x _ => ?_)
    · have h2 : Differentiable ℂ fun z : E => H (z + l) z₀ :=
        (hd z₀).comp (differentiable_id.add_const _)
      have h3 := hd l
      unfold term
      refine Differentiable.differentiableOn ?_
      fun_prop
    · have hx : ∀ᶠ z in 𝓝 x, (H z z).re < (H x x).re + 1 ∧ ‖z - z₀‖ < ‖x - z₀‖ + 1 :=
        (hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _))).and
          ((show Continuous fun z : E => ‖z - z₀‖ by fun_prop).continuousAt.eventually
            (gt_mem_nhds (lt_add_one _)))
      refine ⟨_, hx, _, ((summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left
        (Real.exp (a * (‖x - z₀‖ + 1) ^ 2))).mul_left
        (Real.exp (π / 2 * ((H x x).re + 1 + (H z₀ z₀).re))), fun l z hz => (hle l z).trans ?_⟩
      refine mul_le_mul ?_ (exp_neg_mul_norm_add_sq_le ha.le _ hz.2.le) (Real.exp_pos _).le
        (Real.exp_pos _).le
      gcongr
      exact hz.1.le
  · set A := Real.exp (π / 2 * ((H z₀ z₀).re + (H z₀ z₀).re)) with hA
    have hA0 : 0 < A := Real.exp_pos _
    have hle' : ∀ l : L, ‖term L H χ z₀ l z₀‖ ≤ A * Real.exp (-a * ‖(l : E)‖ ^ 2) := fun l => by
      simpa using hle l z₀
    have hg := summable_lattice_exp_neg_mul_norm_sq L ha
    have hS : Summable fun l : L => term L H χ z₀ l z₀ :=
      .of_norm_bounded (hg.mul_left A) hle'
    have h00 : H 0 0 = 0 := by simpa using hl 0 0 0
    have h0 : ‖term L H χ z₀ 0 z₀‖ = A := by
      rw [norm_term hl hr hs h1]
      simp [h00, hA]
    have hg' : Summable fun l : L => if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2) :=
      .of_nonneg_of_le (fun l => by split_ifs <;> positivity)
        (fun l => by split_ifs <;> [positivity; rfl]) hg
    have h2 : ‖∑' l : L, if l = 0 then 0 else term L H χ z₀ l z₀‖ ≤
        A * ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) := by
      refine tsum_of_norm_bounded (hg'.hasSum.mul_left A) fun l => ?_
      split_ifs
      · simp
      · exact hle' l
    intro h
    beta_reduce at h
    rw [hS.tsum_eq_add_tsum_ite 0, add_eq_zero_iff_eq_neg] at h
    rw [h, norm_neg] at h0
    nlinarith
  · beta_reduce
    rw [← (Equiv.addLeft l).tsum_eq fun m => term L H χ z₀ m z, ← tsum_mul_left]
    exact tsum_congr fun m => term_add hl hr hs h1 hχ z₀ l m z

end General

variable {g : ℕ}

theorem continuous_form (M : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z : Fin g → ℂ => (z ⬝ᵥ M.mulVec (star z)).re := by
  simp only [dotProduct, mulVec]
  fun_prop

theorem exists_coercive (M : Matrix (Fin g) (Fin g) ℂ)
    (hM : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ M.mulVec (star z)).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Fin g → ℂ, c * ‖z‖ ^ 2 ≤ (z ⬝ᵥ M.mulVec (star z)).re := by
  obtain ⟨c, hc, h⟩ := (isCompact_sphere (0 : Fin g → ℂ) 1).exists_forall_le'
    (continuous_form M).continuousOn (a := 0) fun z hz => hM z (by
      rintro rfl
      simp at hz)
  refine ⟨c, hc, fun z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨u, hu, hzu⟩ : ∃ u : Fin g → ℂ, ‖u‖ = 1 ∧ z = (‖z‖ : ℝ) • u :=
    ⟨‖z‖⁻¹ • z, by rw [norm_smul]; simp [hn.ne'], by simp [smul_smul, hn.ne']⟩
  have h2 := h u (by simpa using hu)
  generalize ‖z‖ = r at hn hzu
  subst hzu
  rw [star_smul, star_trivial, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_re, smul_re,
    smul_eq_mul, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg r)]

theorem form_symm {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) (x y : Fin g → ℂ) :
    y ⬝ᵥ M.mulVec (star x) = (starRingEnd ℂ) (x ⬝ᵥ M.mulVec (star y)) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, map_sum, map_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hM.apply j i
  simp only [RCLike.star_def] at this ⊢
  rw [← this, Complex.conj_conj]
  ring

theorem exists_theta_apply_ne_zero :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) := by
  classical
  intro g Λ hΛ _ H₀ hH₀
  obtain ⟨a, ha, hsum⟩ := exists_tsum_gauss_lt_one Λ
  obtain ⟨c, hc, hco⟩ := exists_coercive H₀ hH₀
  refine ⟨a / c, fun Hm χ hH hρ h1 hχ z₀ => ?_⟩
  refine exists_theta (H := fun x y => x ⬝ᵥ Hm.mulVec (star y)) (fun x y w => add_dotProduct ..)
    (fun x y w => by rw [star_add, mulVec_add, dotProduct_add]) (form_symm hH) (fun w => ?_)
    (continuous_form Hm) ha hsum (fun z => ?_) h1 hχ z₀
  · simp only [dotProduct]
    fun_prop
  · have h2 : a * ‖z‖ ^ 2 ≤ (z ⬝ᵥ Hm.mulVec (star z)).re := by
      refine le_trans ?_ (hρ z)
      calc a * ‖z‖ ^ 2 = a / c * (c * ‖z‖ ^ 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hco z) (by positivity)
    have h3 : 0 ≤ a * ‖z‖ ^ 2 := by positivity
    nlinarith [Real.two_le_pi]

end GlobalTheory.ThetaLarge
