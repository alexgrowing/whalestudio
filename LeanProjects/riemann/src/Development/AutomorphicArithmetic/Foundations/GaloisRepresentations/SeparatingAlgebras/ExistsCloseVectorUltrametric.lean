import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

noncomputable section

namespace UpperTheory.Gal.Gen

private theorem exists_close_vector_ultrametric (k : Type) [NormedField k] [IsUltrametricDist k] (X : Type) [Fintype X] (r : ℝ) :
    ∀ (n : ℕ) (P : Submodule k (X → k)) (v : X → k), Module.finrank k P = n →
      (∀ a : X → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) → ‖∑ i, a i * v i‖ ≤ r) →
      ∃ c ∈ P, ∀ i, ‖v i - c i‖ ≤ r := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P v hn h
  by_cases hP : P = ⊥
  · subst hP
    refine ⟨0, Submodule.zero_mem _, fun i => ?_⟩
    have key := h (Pi.single i 1) ?_ ?_
    · simpa [Pi.single_apply] using key
    · intro j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · intro c hc
      have hc0 : c = 0 := by simpa using hc
      simp [hc0]
  · obtain ⟨p0, hp0, hp0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hex : ∃ i, p0 i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hp0ne (funext hcon)
    obtain ⟨j, hj⟩ := hex
    haveI : Nonempty X := ⟨j⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => ‖p0 i‖)
    have hne : p0 i0 ≠ 0 := by
      intro h0
      have h1 := hi0 j
      rw [h0, norm_zero] at h1
      exact hj (norm_le_zero_iff.mp h1)
    obtain ⟨p, hp⟩ : ∃ p, p = (p0 i0)⁻¹ • p0 := ⟨_, rfl⟩
    have hpP : p ∈ P := hp ▸ P.smul_mem _ hp0
    have hpi0 : p i0 = 1 := by simp [hp, hne]
    have hple : ∀ i, ‖p i‖ ≤ 1 := by
      intro i
      simp only [hp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hne)]
      simpa using hi0 i
    obtain ⟨P', hP'⟩ : ∃ P', P' = P ⊓ LinearMap.ker (LinearMap.proj i0 : (X → k) →ₗ[k] k) := ⟨_, rfl⟩
    have hmem : ∀ c, c ∈ P' ↔ c ∈ P ∧ c i0 = 0 := by
      intro c
      simp [hP', Submodule.mem_inf, LinearMap.mem_ker]
    have hlt : P' < P := by
      refine lt_of_le_of_ne (fun c hc => ((hmem c).1 hc).1) ?_
      intro heq
      have h1 : p ∈ P' := heq ▸ hpP
      have h2 := ((hmem p).1 h1).2
      rw [hpi0] at h2
      exact one_ne_zero h2
    have hfr := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨c', hc', hb⟩ := ih _ (hn ▸ hfr) P' (v - v i0 • p) rfl (by
      intro a ha hperp
      obtain ⟨s, hs⟩ : ∃ s, s = ∑ i, a i * p i := ⟨_, rfl⟩
      have hsn : ‖s‖ ≤ 1 := by
        rw [hs]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_one₀ (ha i) (norm_nonneg _) (hple i)
      have hsingle : ∀ w : X → k, ∑ i, (Pi.single i0 s : X → k) i * w i = s * w i0 := by
        intro w
        simp [Pi.single_apply, ite_mul]
      have key := h (a - Pi.single i0 s : X → k) ?_ ?_
      · have e : ∑ i, (a - Pi.single i0 s : X → k) i * v i = ∑ i, a i * (v - v i0 • p) i := by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_sub,
            Finset.sum_sub_distrib, hsingle]
          congr 1
          rw [hs, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rwa [e] at key
      · intro i
        by_cases hi : i = i0
        · subst hi
          simp only [Pi.sub_apply, Pi.single_eq_same]
          rw [sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha _) ?_)
          rwa [norm_neg]
        · simpa [Pi.single_apply, hi] using ha i
      · intro c hc
        have hd : c - c i0 • p ∈ P' := by
          refine (hmem _).2 ⟨P.sub_mem hc (P.smul_mem _ hpP), ?_⟩
          simp [hpi0]
        have h0 := hperp _ hd
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib] at h0
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hsingle]
        have h1 : ∑ i, a i * (c i0 * p i) = c i0 * s := by
          rw [hs, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [h1] at h0
        rw [mul_comm s]
        exact h0)
    refine ⟨v i0 • p + c', P.add_mem (P.smul_mem _ hpP) ((hmem _).1 hc').1, fun i => ?_⟩
    have e : v i - (v i0 • p + c') i = (v - v i0 • p) i - c' i := by
      simp [sub_sub]
    rw [e]
    exact hb i

theorem hB_pf : HB := by
  intro k _ _ X _ P v r h
  exact exists_close_vector_ultrametric k X r _ P v rfl h

end UpperTheory.Gal.Gen

end
