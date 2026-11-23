import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.SpanModel

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem colU_zero (r : ℕ) : colU (E := E) (a := a) r 0 = 1 := by
  ext i j
  simp [colU]

theorem colU_add (r : ℕ) (x y : Fin a → Cinf E) : colU r (x + y) = colU r x * colU r y := by
  apply Units.ext
  change (1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (x + y) i else 0)) =
    ((1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)) *
      (1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then y i else 0)))
  have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
      Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then y i else 0) = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) = r
    · simp [hk]
    · simp [hk]
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, h, add_zero, add_assoc]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> simp

theorem colU_of_le {r : ℕ} (hr : a ≤ r) (x : Fin a → Cinf E) : colU r x = 1 := by
  ext i j
  have : (j : ℕ) ≠ r := by omega
  simp [colU, this]

theorem smoothSpan_le_mspan (π : CuspSub E a) : smoothSpan π ≤ mspan π := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, hf, hφ, rfl⟩
  exact Submodule.mem_sInf.2 fun S hS => hS.2.2.1 _ (hS.1 φ hφ) f hf

theorem mspan_ne_bot (π : CuspSub E a) : mspan π ≠ ⊥ :=
  fun h => smoothSpan_ne_bot π (le_bot_iff.1 (h ▸ smoothSpan_le_mspan π))

def leftInv (E : Type) [Field E] [NumberField E] (a : ℕ) : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ γ g, F (ratGL E a γ * g) = F g}
  add_mem' hF hG γ g := by simp [hF γ g, hG γ g]
  zero_mem' _ _ := rfl
  smul_mem' c F hF γ g := by simp [hF γ g]

theorem mspan_le_leftInv (π : CuspSub E a) : mspan π ≤ leftInv E a := by
  refine sInf_le ⟨fun φ hφ => (π.cusp φ hφ).1.left, fun F hF h γ g => ?_, fun F hF f _ γ g => ?_,
    fun F hF r f γ g => ?_⟩
  · change F (ratGL E a γ * g * h) = F (g * h)
    rw [mul_assoc]; exact hF γ _
  · change smoothInf f F (ratGL E a γ * g) = smoothInf f F g
    rw [← smoothInf_left]
    congr 1
    funext x
    exact hF γ x
  · change colConv r f F (ratGL E a γ * g) = colConv r f F g
    simp only [colConv, mul_assoc]
    congr 1
    funext x
    rw [hF γ]

theorem mspan_left (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ mspan π) (γ : GL (Fin a) E) (g : GA E a) :
    F (ratGL E a γ * g) = F g :=
  mspan_le_leftInv π hF γ g

theorem colConv_integrable (π : CuspSub E a) {φ : Sm E a} (hφ : φ ∈ π.V) (g : GA E a) (r : ℕ)
    (f : SchwartzMap (Fin a → Cinf E) ℂ) :
    Integrable (fun x => f x * φ.1 (g * infGL E a (colU r x))) := by
  haveI : (volume : Measure (Fin a → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

  have hc : Continuous fun x : Fin a → Cinf E => toL (colU r x).val := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun x : Fin a → Cinf E =>
      (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)
    split_ifs
    · exact continuous_const.add (continuous_apply i)
    · exact continuous_const.add continuous_const
  have hF : Continuous fun x : Fin a → Cinf E => φ.1 (g * infGL E a (colU r x)) := by
    have h1 : ContinuousOn (chart φ.1 g) (invSet E a) := (φ.2 g).continuousOn
    have h2 := h1.comp_continuous hc fun x => val_mem_invSet (colU r x)
    refine h2.congr fun x => ?_
    exact chart_val φ.1 g (colU r x)

  obtain ⟨C, N, hC⟩ := (π.cusp φ hφ).1.growth g
  set c₁ : ℝ := ‖(1 : Cinf E)‖
  have hent : ∀ (s : Cinf E) (x : Fin a → Cinf E), ‖s‖ ≤ 1 →
      ‖toL ((1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0))‖ ≤ c₁ + ‖x‖ := by
    intro s x hs
    refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
    change ‖(1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0)‖ ≤ _
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Matrix.one_apply]; split_ifs
      · exact le_rfl
      · simp [c₁]
    · split_ifs
      · exact (norm_mul_le _ _).trans ((mul_le_mul hs (norm_le_pi_norm x i) (norm_nonneg _) zero_le_one).trans (by simp))
      · simp
  have hH : ∀ x : Fin a → Cinf E, height (colU r x) ≤ (1 + 2 * c₁) + 2 * ‖x‖ := by
    intro x
    have e1 : (colU r x).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (1 : Cinf E) * x i else 0) := by
      simp [colU]
    have e2 : ((colU r x)⁻¹).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (-1 : Cinf E) * x i else 0) := by
      change 1 - _ = _
      rw [sub_eq_add_neg]
      congr 1
      ext i j w
      simp only [Matrix.neg_apply, Matrix.of_apply]
      split_ifs <;> simp
    have n1 : ‖(-1 : Cinf E)‖ ≤ 1 := by
      rw [norm_neg]; exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    have n0 : ‖(1 : Cinf E)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    unfold height
    rw [e1, e2]
    linarith [hent 1 x n0, hent (-1) x n1]
  have hC0 : 0 ≤ C := by
    have h := hC 1
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    by_contra hn
    push_neg at hn
    have : C * height (1 : GL (Fin a) (Cinf E)) ^ N < 0 := mul_neg_of_neg_of_pos hn hp
    linarith [norm_nonneg (φ.1 (g * infGL E a 1))]

  set A : ℝ := 1 + 2 * c₁
  have hA : 0 ≤ A := by positivity
  have hdom : Integrable fun x : Fin a → Cinf E => C * ((A + 2 * ‖x‖) ^ N * ‖f x‖) := by
    refine Integrable.const_mul ?_ C
    have e : (fun x : Fin a → Cinf E => (A + 2 * ‖x‖) ^ N * ‖f x‖) = fun x =>
        ∑ m ∈ Finset.range (N + 1), (2 ^ m * A ^ (N - m) * (N.choose m : ℝ)) * (‖x‖ ^ m * ‖f x‖) := by
      funext x
      rw [add_comm, add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_pow]; ring
    rw [e]
    exact integrable_finset_sum _ fun m _ => (f.integrable_pow_mul volume m).const_mul _
  refine Integrable.mono' hdom ((f.continuous.mul hF).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  have hb := (hC (colU r x)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (by linarith [one_le_height (colU r x)]) (hH x) N) hC0)
  calc ‖f x‖ * ‖φ.1 (g * infGL E a (colU r x))‖ ≤ ‖f x‖ * (C * (A + 2 * ‖x‖) ^ N) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = C * ((A + 2 * ‖x‖) ^ N * ‖f x‖) := by ring

end GlobalTheory.JSW.SpanModel
