import Mathlib

open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.two_node_sep (a b a' b' : ℂ) (h : (a, b) ≠ (a', b')) :
    ∃ Q : MvPolynomial (Fin 2) ℂ, eval ![a, b] Q = 1 ∧ eval ![a', b'] Q = 0 := by
  by_cases ha : a = a'
  · have hb : b - b' ≠ 0 := by
      intro hb
      exact h (by rw [ha, sub_eq_zero.mp hb])
    refine ⟨C (b - b')⁻¹ * (X 1 - C b'), ?_, ?_⟩
    · simp [inv_mul_cancel₀ hb]
    · simp
  · have ha' : a - a' ≠ 0 := sub_ne_zero.mpr ha
    refine ⟨C (a - a')⁻¹ * (X 0 - C a'), ?_, ?_⟩
    · simp [inv_mul_cancel₀ ha']
    · simp

private theorem UpperTheory.ConvolutionTheory.FX.two_node_poly (J : Type) [Fintype J] [DecidableEq J] (x z : J → ℂ)
    (h : Function.Injective (fun i => (x i, z i))) (i : J) :
    ∃ P : MvPolynomial (Fin 2) ℂ, ∀ j, eval ![x j, z j] P = if j = i then 1 else 0 := by
  have : ∀ j, ∃ Q : MvPolynomial (Fin 2) ℂ, j ≠ i →
      eval ![x i, z i] Q = 1 ∧ eval ![x j, z j] Q = 0 := by
    intro j
    by_cases hj : j = i
    · exact ⟨0, fun h => absurd hj h⟩
    · obtain ⟨Q, hQ⟩ := UpperTheory.ConvolutionTheory.FX.two_node_sep (x i) (z i) (x j) (z j)
        (fun e => hj (h e).symm)
      exact ⟨Q, fun _ => hQ⟩
  choose Q hQ using this
  refine ⟨∏ j ∈ Finset.univ.erase i, Q j, fun j => ?_⟩
  rw [map_prod]
  split_ifs with hj
  · subst hj
    exact Finset.prod_eq_one fun k hk => (hQ k (Finset.ne_of_mem_erase hk)).1
  · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩) (hQ j hj).2

theorem UpperTheory.ConvolutionTheory.FX.two_node :
    ∀ (J : Type) [Fintype J] (x z : J → ℂ), Function.Injective (fun i => (x i, z i)) → ∃ (s₀ : ℕ) (K : ℝ), ∀ (c : J → ℂ) (ε : ℝ), (∀ s ≤ s₀, ∀ s' ≤ s₀, ‖∑ i, c i * x i ^ s * z i ^ s'‖ ≤ ε) → ∀ i, ‖c i‖ ≤ K * ε := by
  intro J _ x z h
  classical
  choose P hP using UpperTheory.ConvolutionTheory.FX.two_node_poly J x z h
  refine ⟨Finset.univ.sup fun i => (P i).totalDegree,
    ∑ i, ∑ m ∈ (P i).support, ‖(P i).coeff m‖, fun c ε hε i => ?_⟩
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε 0 (Nat.zero_le _) 0 (Nat.zero_le _))
  have h1 : c i = ∑ m ∈ (P i).support, (P i).coeff m * ∑ j, c j * x j ^ m 0 * z j ^ m 1 := by
    have : c i = ∑ j, c j * eval ![x j, z j] (P i) := by
      simp [hP]
    rw [this]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hdeg : ∀ m ∈ (P i).support, ∀ k, m k ≤ Finset.univ.sup fun i => (P i).totalDegree := by
    intro m hm k
    exact ((monomial_le_degreeOf k hm).trans (degreeOf_le_totalDegree _ _)).trans
      (Finset.le_sup (f := fun i => (P i).totalDegree) (Finset.mem_univ i))
  calc ‖c i‖ ≤ ∑ m ∈ (P i).support, ‖(P i).coeff m‖ * ε := by
        rw [h1]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hε _ (hdeg m hm 0) _ (hdeg m hm 1)) (norm_nonneg _)
    _ = (∑ m ∈ (P i).support, ‖(P i).coeff m‖) * ε := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ hε0
        exact Finset.single_le_sum (f := fun i => ∑ m ∈ (P i).support, ‖(P i).coeff m‖)
          (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
