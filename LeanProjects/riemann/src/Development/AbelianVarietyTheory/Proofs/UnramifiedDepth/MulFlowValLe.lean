import Mathlib
import Formalism.DropLevelBounds.Statement
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.FlowScaling

variable {l d : ℕ} [NeZero d]

lemma isFlow_zero {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) : IsFlow l d D (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩

lemma mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    (l : ℝ) * flowVal d x ≤ ∑ a, D a := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  unfold flowVal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have h2 := hx.2 a
  have h3 : 0 ≤ ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i :=
    Finset.sum_nonneg fun i _ => hx.1 _ i
  have h4 : (l : ℝ) * ∑ i ∈ oddLevels d, x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd (Finset.mem_filter.1 hi).2 (by decide)
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)
  linarith

lemma flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ (∑ a, D a) / l := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  rw [le_div_iff₀ hl0, mul_comm]
  exact mul_flowVal_le hl hx

lemma le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  refine le_csSup ⟨(∑ a, D a) / l, ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨y, hy, rfl⟩
  exact flowVal_le hl hy

lemma maxFlow_le {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) {B : ℝ}
    (h : ∀ x, IsFlow l d D x → flowVal d x ≤ B) : maxFlow l d D ≤ B := by
  refine csSup_le ⟨_, _, isFlow_zero hD, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact h y hy

lemma maxFlow_le_div (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d D ≤ (∑ a, D a) / l :=
  maxFlow_le hD fun _ hx => flowVal_le hl hx

lemma maxFlow_nonneg (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    0 ≤ maxFlow l d D := by
  have := le_maxFlow hl (isFlow_zero (l := l) hD)
  simpa [flowVal] using this

lemma mul_maxFlow_le (hl : 1 ≤ l) {c : ℝ} {D D' : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a)
    (h : ∀ a, c * D a ≤ D' a) : c * maxFlow l d D ≤ maxFlow l d D' := by
  rcases hc.eq_or_lt with rfl | hc0
  · rw [zero_mul]
    exact maxFlow_nonneg hl fun a => by simpa using h a
  · rw [← le_div_iff₀' hc0]
    refine maxFlow_le hD fun x hx => ?_
    rw [le_div_iff₀' hc0]
    have hf : IsFlow l d D' (fun a i => c * x a i) := by
      refine ⟨fun s i => mul_nonneg hc (hx.1 s i), fun s => le_trans (le_of_eq ?_)
        ((mul_le_mul_of_nonneg_left (hx.2 s) hc).trans (h s))⟩
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hv : flowVal d (fun a i => c * x a i) = c * flowVal d x := by
      simp only [flowVal, Finset.mul_sum]
    rw [← hv]
    exact le_maxFlow hl hf

lemma maxFlow_mul (hl : 1 ≤ l) {c : ℝ} {D : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d (fun a => c * D a) = c * maxFlow l d D := by
  refine le_antisymm ?_ (mul_maxFlow_le hl hc hD fun _ => le_rfl)
  rcases hc.eq_or_lt with rfl | hc0
  · have := maxFlow_le_div (D := fun a => 0 * D a) hl (fun a => by simp)
    simpa using this
  · have := mul_maxFlow_le (c := c⁻¹) (D := fun a => c * D a) (D' := D) hl (inv_nonneg.2 hc)
      (fun a => mul_nonneg hc (hD a)) (fun a => by rw [inv_mul_cancel_left₀ hc0.ne'])
    rwa [inv_mul_le_iff₀ hc0] at this

theorem fScale : FScale := by
  intro l d _ hl c D hc hD
  unfold Fnum
  rw [maxFlow_mul (by omega) hc hD, ← Finset.mul_sum]
  ring

theorem thetaShift : ThetaShift := by
  intro l d _ hl _ _ n T θ w W th hT hw hW hth hθ
  have hl1 : 1 ≤ l := by omega
  have hl3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hθ0 : 0 ≤ θ := (hth 0).1.trans (hth 0).2
  have hW0 : ∀ a, 0 ≤ W a := fun a => by
    have h1 : 0 ≤ T * W a := by
      rw [hW a]
      exact mul_nonneg (hw a).le (by linarith [(hth a).2])
    exact (mul_nonneg_iff_of_pos_left hT).1 h1
  have hnw : ∀ a, 0 ≤ (n : ℝ) * w a := fun a => mul_nonneg hn (hw a).le
  have h1 : (1 - θ) * maxFlow l d (fun a => (n : ℝ) * w a) ≤
      maxFlow l d (fun a => T * ((n : ℝ) * W a)) := by
    refine mul_maxFlow_le hl1 (by linarith) hnw fun a => ?_
    have e : T * ((n : ℝ) * W a) = (1 - th a) * ((n : ℝ) * w a) := by
      rw [mul_left_comm, hW a]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith [(hth a).2]) (hnw a)
  have h2 : maxFlow l d (fun a => (n : ℝ) * w a) ≤ (∑ a, (n : ℝ) * w a) / l :=
    maxFlow_le_div hl1 hnw
  have h3 : ∑ a, T * ((n : ℝ) * W a) ≤ ∑ a, (n : ℝ) * w a := by
    refine Finset.sum_le_sum fun a _ => ?_
    have e : T * ((n : ℝ) * W a) = (1 - th a) * ((n : ℝ) * w a) := by
      rw [mul_left_comm, hW a]; ring
    rw [e]
    exact mul_le_of_le_one_left (hnw a) (by linarith [(hth a).1])
  have hg : 0 ≤ gam l := div_nonneg (by linarith) (by nlinarith)
  have h4 := mul_le_mul_of_nonneg_left h3 hg
  have h5 := mul_le_mul_of_nonneg_left h2 hθ0
  have h6 : 0 ≤ θ * ((∑ a, (n : ℝ) * w a) / l) :=
    mul_nonneg hθ0 (div_nonneg (Finset.sum_nonneg fun a _ => hnw a) (by linarith))
  have h7 : 6 * θ * n * (∑ a, w a) / l = 6 * (θ * ((∑ a, (n : ℝ) * w a) / l)) := by
    rw [← Finset.mul_sum]; ring
  rw [← fScale l d (by omega) T (fun a => (n : ℝ) * W a) hT.le
    (fun a => mul_nonneg hn (hW0 a)), h7]
  unfold Fnum
  linarith

theorem thetaConst : ThetaConst := by
  intro n m D T hm hD hT h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_iff₀ hm'] at h
  have e : 6 * ((D + 4) / T) * n = 6 * (D + 4) * n / T := by ring
  rw [e, div_le_iff₀ hT]
  nlinarith [mul_nonneg hn (sub_nonneg.2 hD)]

theorem main : FScale ∧ ThetaShift ∧ ThetaConst := ⟨fScale, thetaShift, thetaConst⟩

end GlobalTheory.FlowScaling
