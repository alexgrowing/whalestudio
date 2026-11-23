import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory

theorem sepFamily_prod : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (F : Subfield L) (ι : Type) (s : Finset ι) (x y : ι → L), (∀ j ∈ s, x j ∈ F ∧ y j ∈ F ∧ v (x j) ≤ 1 ∧ v (y j) ≤ 1) → ∃ (n : ℕ) (a b : Fin n → L), (∀ i, a i ∈ F ∧ b i ∈ F ∧ v (a i) ≤ 1 ∧ v (b i) ≤ 1) ∧ ∀ σ : G, ∑ i, a i * σ • b i = ∏ j ∈ s, (x j - σ • y j) := by
  intro L _ v G _ _ F ι s x y hs
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, fun _ => 1, fun _ => 1, fun _ => ⟨F.one_mem, F.one_mem, by simp, by simp⟩,
      fun σ => by simp⟩
  | insert j s hj ih =>
    obtain ⟨n, a, b, hab, hsum⟩ := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
    obtain ⟨hxF, hyF, hxv, hyv⟩ := hs j (Finset.mem_insert_self j s)
    refine ⟨n + n, Fin.append (fun i => x j * a i) (fun i => - a i),
      Fin.append b (fun i => y j * b i), ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.mul_mem hxF h1, h2, by rw [map_mul]; exact mul_le_one' hxv h3, h4⟩
      · simp only [Fin.append_right]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.neg_mem h1, F.mul_mem hyF h2, by rw [Valuation.map_neg]; exact h3,
          by rw [map_mul]; exact mul_le_one' hyv h4⟩
    · intro σ
      rw [Finset.prod_insert hj, ← hsum σ, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, smul_mul']
      have e1 : ∑ i, x j * a i * σ • b i = x j * ∑ i, a i * σ • b i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      have e2 : ∑ i, -a i * (σ • y j * σ • b i) = -(σ • y j * ∑ i, a i * σ • b i) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e1, e2]; ring

end GlobalTheory
