import Mathlib
import Formalism.DropLevelBounds.Statement
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.FlowParameters

lemma sum_inflow (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : Finset ℕ) :
    ∑ a : ZMod d, ∑ i ∈ s, x (a - (i : ZMod d)) i = ∑ a, ∑ i ∈ s, x a i := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)

lemma flowVal_le_sum (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d D x) : flowVal d x ≤ ∑ a, D a := by
  unfold flowVal
  rw [← sum_inflow]
  refine Finset.sum_le_sum fun a _ => ?_
  have h1 := hx.2 a
  have h2 : 0 ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hx.1 a i)
  linarith

lemma flowVal_le_maxFlow (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d D x) : flowVal d x ≤ maxFlow l d D := by
  refine le_csSup ⟨∑ a, D a, ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨z, hz, rfl⟩
  exact flowVal_le_sum l d D z hz

lemma maxFlow_smul_le (l d : ℕ) [NeZero d] (c : ℝ) (hc : 0 ≤ c) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    maxFlow l d (fun a => c * D a) ≤ c * maxFlow l d D := by
  refine csSup_le ⟨_, fun _ _ => 0, ⟨fun _ _ => le_rfl, fun s => ?_⟩, rfl⟩ ?_
  · simpa using mul_nonneg hc (hD s)
  rintro t ⟨x, hx, rfl⟩
  rcases hc.eq_or_lt with rfl | hc'
  · simpa using flowVal_le_sum l d _ x hx
  · have hz : IsFlow l d D (fun a i => c⁻¹ * x a i) := by
      refine ⟨fun s i => mul_nonneg (by positivity) (hx.1 s i), fun s => ?_⟩
      have h := hx.2 s
      have e : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * (c⁻¹ * x s i)) +
          (∑ i ∈ oddLevels d, c⁻¹ * x (s - (i : ZMod d)) i) =
          c⁻¹ * ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
            (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i)) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, inv_mul_le_iff₀ hc']
      exact h
    have h := flowVal_le_maxFlow l d D _ hz
    have e : flowVal d (fun a i => c⁻¹ * x a i) = c⁻¹ * flowVal d x := by
      simp only [flowVal, Finset.mul_sum]
    rw [e, inv_mul_le_iff₀ hc'] at h
    exact h

theorem sizeDataSmall : ParametersSmall := by
  intro l d _ hl hd n m θ S W ys y u mon cCH cMON cB eB hW _ hval _ hS hzero _ hmon hsplit
    hB hCH hMON
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hg : 0 ≤ gam l := div_nonneg (by positivity) (by nlinarith)
  have hn : (0 : ℝ) ≤ n := by positivity
  have hscale := maxFlow_smul_le l d n hn W hW

  have hWsum : ∑ a, W a = (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) + (∑ a, u a) + ∑ a, mon a := by
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_inflow d (fun a i => (y a i : ℝ))]

  have hBsum : ∑ a, ∑ i ∈ oddLevels d, cB a i ≤
      n * gam l * (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        (n * gam l - n) * (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) +
        ∑ a, ∑ i ∈ oddLevels d, eB a i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i hi => ?_
    have := hB a i hi
    linarith
  have hCHsum : ∑ a, cCH a ≤ n * gam l * (∑ a, u a) + m * (∑ a, u a) / ((l : ℝ) - 1) := by
    refine (Finset.sum_le_sum fun a _ => hCH a).trans (le_of_eq ?_)
    rw [← Finset.sum_mul]
    ring
  have hMONsum : ∑ a, cMON a ≤ (∑ a, mon a) / ((l : ℝ) - 1) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun a _ => hMON a

  have hround : flowVal d ys ≤ (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) +
      S * (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
        (fun p => ys p.1 p.2 ≠ 0)).card := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Finset.sum_product,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : ys a i = 0
    · simp [h]
    · have := hS a i
      simp only [ne_eq, h, not_false_eq_true, if_true, Nat.cast_one, mul_one]
      linarith
  have hmonsum : 0 ≤ n * gam l * ∑ a, mon a :=
    mul_nonneg (mul_nonneg hn hg) (Finset.sum_nonneg fun a _ => hmon a)
  have h1 := mul_le_mul_of_nonneg_left (hval.trans hround) hn
  have h2 : gam l * ∑ a, (n : ℝ) * W a = n * gam l * ∑ a, W a := by
    rw [← Finset.mul_sum]; ring
  have h3 := congrArg (fun t => n * gam l * t) hWsum
  unfold Fnum
  rw [h2]
  linarith

end GlobalTheory.FlowParameters
