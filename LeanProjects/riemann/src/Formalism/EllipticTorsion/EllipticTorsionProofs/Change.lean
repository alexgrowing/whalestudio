import Mathlib
import Formalism.EllipticTorsion.ChangeIntegral

open Formalism.ELL Formalism.G

namespace Formalism.ELL.RootExponentBounds

universe u

section
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma addle {x y : K} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x + y‖ ≤ B :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

lemma tb {a r : K} (k n : ℕ) (ha : ‖a‖ ≤ 1) (hr : 1 ≤ ‖r‖) (hk : k ≤ n) :
    ‖a * r ^ k‖ ≤ ‖r‖ ^ n := by
  rw [norm_mul, norm_pow]
  calc ‖a‖ * ‖r‖ ^ k ≤ 1 * ‖r‖ ^ n :=
        mul_le_mul ha (pow_le_pow_right₀ hr hk) (by positivity) zero_le_one
    _ = _ := one_mul _

lemma root2 {a b r : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (h : r ^ 2 + a * r + b = 0) :
    ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e : r ^ 2 = -(a * r ^ 1 + b * r ^ 0) := by linear_combination h
  have hb' : ‖a * r ^ 1 + b * r ^ 0‖ ≤ ‖r‖ ^ 1 :=
    addle (tb 1 1 ha hr.le le_rfl) (tb 0 1 hb hr.le (by norm_num))
  rw [← norm_neg, ← e, norm_pow] at hb'
  have : ‖r‖ ^ 1 < ‖r‖ ^ 2 := pow_lt_pow_right₀ hr (by norm_num)
  linarith

lemma root3 {c a b d r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (h : c * r ^ 3 + a * r ^ 2 + b * r + d = 0) : ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e : c * r ^ 3 = -(a * r ^ 2 + b * r ^ 1 + d * r ^ 0) := by linear_combination h
  have hb' : ‖a * r ^ 2 + b * r ^ 1 + d * r ^ 0‖ ≤ ‖r‖ ^ 2 :=
    addle (addle (tb 2 2 ha hr.le le_rfl) (tb 1 2 hb hr.le (by norm_num)))
      (tb 0 2 hd hr.le (by norm_num))
  rw [← norm_neg, ← e, norm_mul, norm_pow, hc, one_mul] at hb'
  have : ‖r‖ ^ 2 < ‖r‖ ^ 3 := pow_lt_pow_right₀ hr (by norm_num)
  linarith

lemma root4 {c a b d e r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (he : ‖e‖ ≤ 1) (h : c * r ^ 4 + a * r ^ 3 + b * r ^ 2 + d * r + e = 0) : ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e' : c * r ^ 4 = -(a * r ^ 3 + b * r ^ 2 + d * r ^ 1 + e * r ^ 0) := by
    linear_combination h
  have hb' : ‖a * r ^ 3 + b * r ^ 2 + d * r ^ 1 + e * r ^ 0‖ ≤ ‖r‖ ^ 3 :=
    addle (addle (addle (tb 3 3 ha hr.le le_rfl) (tb 2 3 hb hr.le (by norm_num)))
      (tb 1 3 hd hr.le (by norm_num))) (tb 0 3 he hr.le (by norm_num))
  rw [← norm_neg, ← e', norm_mul, norm_pow, hc, one_mul] at hb'
  have : ‖r‖ ^ 3 < ‖r‖ ^ 4 := pow_lt_pow_right₀ hr (by norm_num)
  linarith

lemma memB {x : K} : x ∈ unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

lemma natB (n : ℕ) : (n : K) ∈ unitBall K := memB.2 (IsUltrametricDist.norm_natCast_le_one K n)

lemma ofNatB (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : K) ∈ unitBall K := by
  have := natB (K := K) n
  exact this

end

macro "change_aux_intm" : tactic => `(tactic| (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem)))

lemma bmem {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (h1 : W.a₁ ∈ unitBall K) (h2 : W.a₂ ∈ unitBall K) (h3 : W.a₃ ∈ unitBall K)
    (h4 : W.a₄ ∈ unitBall K) (h6 : W.a₆ ∈ unitBall K) :
    W.b₂ ∈ unitBall K ∧ W.b₄ ∈ unitBall K ∧ W.b₆ ∈ unitBall K ∧ W.b₈ ∈ unitBall K := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [WeierstrassCurve.b₂]; change_aux_intm
  · simp only [WeierstrassCurve.b₄]; change_aux_intm
  · simp only [WeierstrassCurve.b₆]; change_aux_intm
  · simp only [WeierstrassCurve.b₈]; change_aux_intm

theorem change_of_variables_integral_of : ChangeIntegral.{u} := by
  intro K _ _ W C hW hW' hΔ0 hΔ
  set W' := C • W with hW'def
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  obtain ⟨h1', h2', h3', h4', h6'⟩ := hW'

  have hv : ‖((C.u⁻¹ : Kˣ) : K)‖ = 1 := by
    have e := WeierstrassCurve.variableChange_Δ W C
    rw [← hW'def] at e
    rw [e, norm_mul, norm_pow] at hΔ
    have hn : ‖W.Δ‖ ≠ 0 := norm_ne_zero_iff.2 hΔ0
    have : ‖((C.u⁻¹ : Kˣ) : K)‖ ^ 12 = 1 := by
      have := mul_right_cancel₀ hn (hΔ.trans (one_mul _).symm); exact this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  have hu : ‖(C.u : K)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_eq_one] at hv; exact hv
  set u : K := (C.u : K)
  set v : K := ((C.u⁻¹ : Kˣ) : K)
  have hvu : v * u = 1 := by simp [u, v]
  have hvu2 : v ^ 2 * u ^ 2 = 1 := by rw [← mul_pow, hvu, one_pow]
  have hvu6 : v ^ 6 * u ^ 6 = 1 := by rw [← mul_pow, hvu, one_pow]
  have hvu8 : v ^ 8 * u ^ 8 = 1 := by rw [← mul_pow, hvu, one_pow]
  rw [← memB] at h1 h2 h3 h4 h6 h1' h2' h3' h4' h6'
  have hu' : u ∈ unitBall K := by rw [memB, hu]
  obtain ⟨hb2, hb4, hb6, hb8⟩ := bmem W h1 h2 h3 h4 h6
  obtain ⟨-, -, hb6', hb8'⟩ := bmem W' h1' h2' h3' h4' h6'

  have hr : C.r ∈ unitBall K := by
    rw [memB]
    rcases (IsUltrametricDist.norm_natCast_le_one K 2).lt_or_eq with h2lt | h2eq
    ·
      have h3n : ‖(3 : K)‖ = 1 := by
        have h3le : ‖(3 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 3
        have : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
          have := IsUltrametricDist.norm_add_le_max (3 : K) (-2)
          rw [norm_neg] at this
          have e : (3 : K) + -2 = 1 := by norm_num
          rwa [e] at this
        rw [norm_one] at this
        push_cast at h2lt
        rcases le_max_iff.1 this with h | h
        · exact le_antisymm h3le h
        · linarith
      have e8 := WeierstrassCurve.variableChange_b₈ W C
      rw [← hW'def] at e8
      have key : (3 : K) * C.r ^ 4 + W.b₂ * C.r ^ 3 + (3 * W.b₄) * C.r ^ 2 + (3 * W.b₆) * C.r
          + (W.b₈ - u ^ 8 * W'.b₈) = 0 := by
        linear_combination (-u ^ 8) * e8 - (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄
          + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) * hvu8
      refine root4 h3n (memB.1 hb2) (memB.1 (by change_aux_intm)) (memB.1 (by change_aux_intm)) (memB.1 (by change_aux_intm)) key
    ·
      have h4n : ‖(4 : K)‖ = 1 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this, norm_mul]; push_cast at h2eq; rw [h2eq]; norm_num
      have e6 := WeierstrassCurve.variableChange_b₆ W C
      rw [← hW'def] at e6
      have key : (4 : K) * C.r ^ 3 + W.b₂ * C.r ^ 2 + (2 * W.b₄) * C.r
          + (W.b₆ - u ^ 6 * W'.b₆) = 0 := by
        linear_combination (-u ^ 6) * e6 - (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂
          + 4 * C.r ^ 3) * hvu6
      exact root3 h4n (memB.1 hb2) (memB.1 (by change_aux_intm)) (memB.1 (by change_aux_intm)) key

  have hs : C.s ∈ unitBall K := by
    have e2 : W'.a₂ = v ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := rfl
    have key : C.s ^ 2 + W.a₁ * C.s + (-W.a₂ - 3 * C.r + u ^ 2 * W'.a₂) = 0 := by
      linear_combination u ^ 2 * e2 + (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * hvu2
    exact memB.2 (root2 (memB.1 h1) (memB.1 (by change_aux_intm)) key)

  have ht : C.t ∈ unitBall K := by
    have e6 : W'.a₆ = v ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
        - C.t ^ 2 - C.r * C.t * W.a₁) := rfl
    have key : C.t ^ 2 + (W.a₃ + C.r * W.a₁) * C.t
        + (-(W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3) + u ^ 6 * W'.a₆) = 0 := by
      linear_combination u ^ 6 * e6 + (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
        - C.t ^ 2 - C.r * C.t * W.a₁) * hvu6
    exact memB.2 (root2 (memB.1 (by change_aux_intm)) (memB.1 (by change_aux_intm)) key)
  exact ⟨hu, memB.1 hr, memB.1 hs, memB.1 ht⟩

end Formalism.ELL.RootExponentBounds

namespace Formalism.ELL

universe v

theorem change_of_variables_integral : ChangeIntegral.{v} := Formalism.ELL.RootExponentBounds.change_of_variables_integral_of

end Formalism.ELL
