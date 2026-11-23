import Mathlib

noncomputable section

namespace GlobalTheory.LatticeSchwartz

theorem summable_one_add_norm_inv_pow' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ}
    (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

theorem term_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h f : SchwartzMap V ℂ) (k N j m : ℕ) (x l : V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ m f (x - l)‖ ≤
      (2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, m)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) *
      ((1 + ‖l‖)⁻¹) ^ N := by
  have hA := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, j)) le_rfl le_rfl h x
  have hB := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, m)) le_rfl le_rfl f (x - l)
  have hc : 1 + ‖l‖ ≤ (1 + ‖x‖) * (1 + ‖x - l‖) := by
    have : ‖l‖ ≤ ‖x‖ + ‖x - l‖ := by
      calc ‖l‖ = ‖x - (x - l)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - l‖ := norm_sub_le _ _
    nlinarith [norm_nonneg x, norm_nonneg (x - l)]
  have hc0 : 0 < 1 + ‖l‖ := by positivity
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
  set P := ‖iteratedFDeriv ℝ j h x‖
  set Q := ‖iteratedFDeriv ℝ m f (x - l)‖
  have hP : 0 ≤ P := norm_nonneg _
  have hQ : 0 ≤ Q := norm_nonneg _
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖x‖ ^ k * P * Q * (1 + ‖l‖) ^ N
      ≤ (1 + ‖x‖) ^ k * P * Q * ((1 + ‖x‖) * (1 + ‖x - l‖)) ^ N := by gcongr
    _ = ((1 + ‖x‖) ^ (k + N) * P) * ((1 + ‖x - l‖) ^ N * Q) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr

theorem summable_seminorm_mul_comp_sub : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h x * f (x - l)) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  intro V _ _ _ Λ _ _ h f _ u hu k n
  set N := Module.finrank ℤ Λ + 1 with hN
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set D : ℕ → ℝ := fun j => (n.choose j : ℝ) *
      ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by
    have h1 : 0 ≤ (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h := apply_nonneg _ _
    have h2 : 0 ≤ (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f := apply_nonneg _ _
    positivity
  set C := ∑ j ∈ Finset.range (n + 1), D j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => hD0 j
  refine Summable.of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_) (hw.mul_left C)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) fun x => ?_
  have hul : (u l : V → ℂ) = fun y => h y * f (y - l) := funext (hu l)
  rw [hul]
  have hg : ContDiff ℝ n (fun y : V => f (y - (l : V))) :=
    (f.smooth n).comp (contDiff_id.sub contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (h.smooth n) hg x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_sub] at hL
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h y * f (y - l)) x‖
      ≤ ‖x‖ ^ k * ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖ := by
        gcongr
    _ = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ Finset.range (n + 1), D j * ((1 + ‖(l : V)‖)⁻¹) ^ N := by
        refine Finset.sum_le_sum fun j _ => ?_
        have ht := term_le h f k N j (n - j) x l
        have hch : (0 : ℝ) ≤ n.choose j := Nat.cast_nonneg _
        calc (n.choose j : ℝ) *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖)
            ≤ (n.choose j : ℝ) * ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup
                (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
              (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) *
              ((1 + ‖(l : V)‖)⁻¹) ^ N) := mul_le_mul_of_nonneg_left ht hch
          _ = D j * ((1 + ‖(l : V)‖)⁻¹) ^ N := by rw [hD]; ring
    _ = C * ((1 + ‖l‖)⁻¹) ^ N := by rw [hC, Finset.sum_mul]; rfl

end GlobalTheory.LatticeSchwartz
