import Mathlib
open MeasureTheory

namespace GlobalTheory

noncomputable section

theorem summable_norm_and_tsum_prod_fin (α : Type) (n : ℕ) (f : Fin n → α → ℂ)
    (hf : ∀ k, Summable fun a => ‖f k a‖) :
    (Summable fun m : Fin n → α => ‖∏ k, f k (m k)‖) ∧
      ∑' m : Fin n → α, ∏ k, f k (m k) = ∏ k, ∑' a, f k a := by
  induction n with
  | zero => exact ⟨Summable.of_finite, by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fun k => f k.succ) fun k => hf _
    have e : ∀ q : α × (Fin n → α), ∏ k, f k ((Fin.consEquiv fun _ => α) q k) =
        f 0 q.1 * ∏ k : Fin n, f k.succ (q.2 k) := by
      intro q; rw [Fin.prod_univ_succ]; rfl
    constructor
    · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => α).summable_iff]
      have := (hf 0).mul_norm h1
      simpa only [Function.comp_def, e] using this
    · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => α).tsum_eq, Fin.prod_univ_succ, ← h2,
        tsum_mul_tsum_of_summable_norm (hf 0) h1]
      simp only [e]

theorem summable_norm_and_tsum_prod_fintype (κ α : Type) [Fintype κ] (f : κ → α → ℂ)
    (hf : ∀ k, Summable fun a => ‖f k a‖) :
    (Summable fun m : κ → α => ‖∏ k, f k (m k)‖) ∧
      ∑' m : κ → α, ∏ k, f k (m k) = ∏ k, ∑' a, f k a := by
  set e := (Fintype.equivFin κ).symm
  obtain ⟨h1, h2⟩ := summable_norm_and_tsum_prod_fin α _ (fun k => f (e k)) fun k => hf _
  let E : (Fin (Fintype.card κ) → α) ≃ (κ → α) := e.arrowCongr (Equiv.refl α)
  have h : ∀ m : Fin (Fintype.card κ) → α, ∏ k, f k (E m k) = ∏ k, f (e k) (m k) := by
    intro m; rw [← e.prod_comp]; simp [E, Equiv.arrowCongr_apply]
  constructor
  · rw [← E.summable_iff]; simpa only [Function.comp_def, h] using h1
  · rw [← E.tsum_eq]; simp only [h]; rw [h2, ← e.prod_comp]

theorem geom_zpow_ge (a : ℤ) (r : ℂ) (hr0 : r ≠ 0) (hr : ‖r‖ < 1) :
    Summable (fun k : ℤ => ‖if a ≤ k then r ^ k else 0‖) ∧
      HasSum (fun k : ℤ => if a ≤ k then r ^ k else 0) (r ^ a * (1 - r)⁻¹) := by
  have hinj : Function.Injective (fun n : ℕ => a + (n : ℤ)) := by
    intro m n h; simpa using h
  have hout : ∀ k : ℤ, k ∉ Set.range (fun n : ℕ => a + (n : ℤ)) → ¬ a ≤ k := by
    intro k hk hak
    exact hk ⟨(k - a).toNat, by simp [Int.toNat_of_nonneg (sub_nonneg.2 hak)]⟩
  have hcomp : ∀ n : ℕ, (if a ≤ a + (n : ℤ) then r ^ (a + (n : ℤ)) else 0) = r ^ a * r ^ n := by
    intro n
    rw [if_pos (by omega), zpow_add₀ hr0, zpow_natCast]
  constructor
  · rw [← hinj.summable_iff (fun k hk => by simp [hout k hk])]
    have : Summable fun n : ℕ => ‖r‖ ^ a * ‖r‖ ^ n :=
      (summable_geometric_of_lt_one (norm_nonneg _) hr).mul_left _
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, hcomp, norm_mul, norm_zpow, norm_pow]
  · rw [← hinj.hasSum_iff (fun k hk => by simp [hout k hk])]
    have := (hasSum_geometric_of_norm_lt_one hr).mul_left (r ^ a)
    refine this.congr_fun fun n => ?_
    simp only [Function.comp_apply, hcomp]

theorem tsum_prod_geom_zpow_ge : ∀ {ι : Type} [Fintype ι] (a : ι → ℤ) (r : ι → ℂ), (∀ i, r i ≠ 0) → (∀ i, ‖r i‖ < 1) →
    Summable (fun k : ι → ℤ => ‖if (∀ i, a i ≤ k i) then ∏ i, r i ^ k i else 0‖) ∧
    ∑' k : ι → ℤ, (if (∀ i, a i ≤ k i) then ∏ i, r i ^ k i else 0) = ∏ i, r i ^ a i * (1 - r i)⁻¹ := by
  intro ι _ a r hr0 hr
  classical
  have hg := fun i => geom_zpow_ge (a i) (r i) (hr0 i) (hr i)
  obtain ⟨h1, h2⟩ := summable_norm_and_tsum_prod_fintype ι ℤ
    (fun i k => if a i ≤ k then r i ^ k else 0) fun i => (hg i).1
  have hprod : ∀ k : ι → ℤ, (∏ i, (if a i ≤ k i then r i ^ k i else 0)) =
      if (∀ i, a i ≤ k i) then ∏ i, r i ^ k i else 0 := by
    intro k
    split_ifs with h
    · exact Finset.prod_congr rfl fun i _ => if_pos (h i)
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (not_le.2 hi))
  refine ⟨by simpa only [hprod] using h1, ?_⟩
  simp only [hprod] at h2
  rw [h2]
  exact Finset.prod_congr rfl fun i _ => (hg i).2.tsum_eq

end

end GlobalTheory
