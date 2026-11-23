import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob

noncomputable section

open GlobalTheory.Cong MvPolynomial

namespace UpperTheory.Gal.Gen

variable {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type}

private theorem polyApprox_cut {η : J → k} {T : Set (J → k)} {Q : MvPolynomial J ℤ} (hQ : aeval η Q ≠ 0)
    (h : PolyApprox η T) : PolyApprox η {x | x ∈ T ∧ aeval x Q ≠ 0} := by
  classical
  intro ε hε
  have hq : 0 < ‖aeval η Q‖ := norm_pos_iff.2 hQ
  obtain ⟨s, c, hs, hc⟩ := h (ε * ‖aeval η Q‖) (mul_pos hε hq)
  refine ⟨s.filter (fun x => aeval x Q ≠ 0), fun x => c x * aeval x Q / aeval η Q, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    exact ⟨hs hx.1, hx.2⟩
  · intro P
    have e1 : ∑ x ∈ s.filter (fun x => aeval x Q ≠ 0), c x * aeval x Q / aeval η Q * aeval x P
        = (∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q := by
      rw [Finset.sum_filter_of_ne, Finset.sum_div]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [map_mul]
        ring
      · intro x _ hx hQx
        apply hx
        simp [hQx]
    rw [e1]
    have e2 : aeval η P - (∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q
        = (aeval η (P * Q) - ∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q := by
      rw [map_mul, sub_div, mul_div_assoc, div_self hQ, mul_one]
    rw [e2, norm_div, div_le_iff₀ hq]
    exact hc (P * Q)

private theorem polyApprox_trans {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hS : ∀ η ∈ S, PolyApprox η T) : PolyApprox θ T := by
  classical
  intro ε hε
  obtain ⟨s, c, hs, hc⟩ := h (ε / 2) (by positivity)
  have hM0 : 0 ≤ ∑ η ∈ s, ‖c η‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hε2 : 0 < ε / (2 * (∑ η ∈ s, ‖c η‖ + 1)) := by positivity
  have hT : ∀ η ∈ S, ∃ (t : Finset (J → k)) (d : (J → k) → k), (↑t : Set (J → k)) ⊆ T ∧
      ∀ P : MvPolynomial J ℤ, ‖aeval η P - ∑ ζ ∈ t, d ζ * aeval ζ P‖
        ≤ ε / (2 * (∑ η ∈ s, ‖c η‖ + 1)) :=
    fun η hη => hS η hη _ hε2
  choose! t d ht hd using hT
  refine ⟨s.biUnion t, fun ζ => ∑ η ∈ s, c η * (if ζ ∈ t η then d η ζ else 0), ?_, ?_⟩
  · intro ζ hζ
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop] at hζ
    obtain ⟨η, hη, hζ⟩ := hζ
    exact ht η (hs hη) hζ
  · intro P
    have hsum : ∑ ζ ∈ s.biUnion t, (∑ η ∈ s, c η * (if ζ ∈ t η then d η ζ else 0)) * aeval ζ P
        = ∑ η ∈ s, c η * ∑ ζ ∈ t η, d η ζ * aeval ζ P := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun η hη => ?_
      rw [Finset.mul_sum]
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.subset_biUnion_of_mem t hη)
      · intro ζ hζ
        rw [if_neg (Finset.mem_sdiff.1 hζ).2]
        ring
      · intro ζ hζ
        rw [if_pos hζ]
        ring
    rw [hsum]
    have split : aeval θ P - ∑ η ∈ s, c η * ∑ ζ ∈ t η, d η ζ * aeval ζ P
        = (aeval θ P - ∑ η ∈ s, c η * aeval η P)
          + ∑ η ∈ s, c η * (aeval η P - ∑ ζ ∈ t η, d η ζ * aeval ζ P) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [split]
    calc _ ≤ ‖aeval θ P - ∑ η ∈ s, c η * aeval η P‖
          + ‖∑ η ∈ s, c η * (aeval η P - ∑ ζ ∈ t η, d η ζ * aeval ζ P)‖ := norm_add_le _ _
      _ ≤ ε / 2 + ∑ η ∈ s, ‖c η‖ * (ε / (2 * (∑ η ∈ s, ‖c η‖ + 1))) := by
          gcongr
          · exact hc P
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun η hη => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hd η (hs hη) P) (norm_nonneg _)
      _ ≤ ε := by
          rw [← Finset.sum_mul]
          generalize ∑ η ∈ s, ‖c η‖ = M at hM0 ⊢
          have h1 : M / (M + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          have h2 : M * (ε / (2 * (M + 1))) = ε / 2 * (M / (M + 1)) := by
            field_simp
          have h3 : ε / 2 * (M / (M + 1)) ≤ ε / 2 := mul_le_of_le_one_right (by positivity) h1
          linarith

theorem combine_pf : Combine := by
  intro k _ _ J θ S T Q hθ h
  exact polyApprox_trans hθ fun η hη => polyApprox_cut (h η hη).1 (h η hη).2

end UpperTheory.Gal.Gen

end
