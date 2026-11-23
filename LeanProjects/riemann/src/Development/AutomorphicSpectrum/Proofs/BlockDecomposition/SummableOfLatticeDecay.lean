import Mathlib
open MeasureTheory

namespace GlobalTheory.CompanionTheory.LatticeCount

theorem summable_inv_one_add_sq_int :
    Summable (fun m : ℤ => ((1 : ℝ) + (m : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually h ?_
  have hfin : ({0} : Set ℤ).Finite := Set.finite_singleton 0
  refine Filter.mem_cofinite.2 (hfin.subset ?_)
  intro m hm
  by_contra h0
  have h0' : m ≠ 0 := by simpa using h0
  apply hm
  have hm0 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast h0'
    positivity
  have hpos : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
  show ‖((1 : ℝ) + (m : ℝ) ^ 2)⁻¹‖ ≤ 1 / (m : ℝ) ^ 2
  rw [Real.norm_of_nonneg (inv_nonneg.2 hpos.le), one_div]
  exact inv_anti₀ hm0 (by linarith)

theorem summable_prod_inv_one_add_sq (d : ℕ) :
    Summable (fun n : Fin d → ℤ => ∏ k, ((1 : ℝ) + (n k : ℝ) ^ 2)⁻¹) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
    have h2 := summable_inv_one_add_sq_int.mul_of_nonneg ih
      (fun m => by positivity) (fun n => Finset.prod_nonneg (fun k _ => by positivity))
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff]
    refine h2.congr ?_
    intro x
    simp [Fin.prod_univ_succ, Fin.consEquiv]
    exact mul_comm _ _

theorem summable_of_lattice_decay (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ)
    (hf : Function.Injective f) (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hC : ∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C)
    (hint : ∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) : Summable w := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let S := {i // w i ≠ 0}
  choose n hn using fun i : S => hint i.1 i.2
  have hinj : Function.Injective n := by
    intro a b hab
    apply Subtype.ext
    apply hf
    funext k
    have h1 := hn a k
    have h2 := hn b k
    rw [hab] at h1
    exact mul_left_cancel₀ hNpos.ne' (h1.trans h2.symm)
  have hg := ((summable_prod_inv_one_add_sq d).comp_injective hinj).mul_left (((N : ℝ) ^ 2) ^ d * C)
  have hbound : ∀ a : S, ‖w a.1‖ ≤ ((N : ℝ) ^ 2) ^ d * C *
      ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)⁻¹ := by
    intro a
    have hle : ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) ≤
        ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) := by
      have : ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) =
          ∏ k : Fin d, ((N : ℝ) ^ 2 * (1 + f a.1 k ^ 2)) := by
        rw [Finset.prod_mul_distrib]; simp
      rw [this]
      refine Finset.prod_le_prod (fun k _ => by positivity) (fun k _ => ?_)
      rw [← hn a k]
      have : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hpos : (0 : ℝ) < ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) :=
      Finset.prod_pos (fun k _ => by positivity)
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖w a.1‖ * ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)
        ≤ ‖w a.1‖ * (((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ((N : ℝ) ^ 2) ^ d * (‖w a.1‖ * ∏ k, (1 + f a.1 k ^ 2)) := by ring
      _ ≤ ((N : ℝ) ^ 2) ^ d * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hsub : Summable (w ∘ (Subtype.val : S → ι)) :=
    Summable.of_norm_bounded hg hbound
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).1 hsub
  intro x hx
  by_contra h0
  exact hx ⟨⟨x, h0⟩, rfl⟩

end GlobalTheory.CompanionTheory.LatticeCount
