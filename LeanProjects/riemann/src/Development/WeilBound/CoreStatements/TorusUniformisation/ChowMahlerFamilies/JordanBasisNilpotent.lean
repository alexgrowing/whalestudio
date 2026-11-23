import Mathlib

namespace PositivityTheory.Xgn.JordanBasis

theorem exists_span_sup_range {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (π : Module.End k W) (r : ℕ)
    (h : Module.finrank k (LinearMap.ker π) ≤ r) :
    ∃ x : Fin r → W, ∀ v : W, ∃ a ∈ Submodule.span k (Set.range x), ∃ u : W, v = a + π u := by
  classical
  have hd : Module.finrank k (W ⧸ LinearMap.range π) ≤ r := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range π)
    have h2 := LinearMap.finrank_range_add_finrank_ker π
    omega
  obtain ⟨g, hg⟩ : ∃ g : W ⧸ LinearMap.range π → W, ∀ q, (LinearMap.range π).mkQ (g q) = q :=
    ⟨_, Function.surjInv_eq (LinearMap.range π).mkQ_surjective⟩
  let b := Module.finBasis k (W ⧸ LinearMap.range π)
  let x : Fin r → W := fun i =>
    if h : (i : ℕ) < Module.finrank k (W ⧸ LinearMap.range π) then g (b ⟨i, h⟩) else 0
  have hspan : ∀ j, g (b j) ∈ Submodule.span k (Set.range x) := by
    intro j
    apply Submodule.subset_span
    refine ⟨⟨j, lt_of_lt_of_le j.2 hd⟩, ?_⟩
    simp [x, j.2]
  refine ⟨x, fun v => ?_⟩
  refine ⟨∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hspan j), ?_⟩
  have hq : (LinearMap.range π).mkQ
      (v - ∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j)) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul, hg]
    rw [b.sum_repr, sub_self]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hq
  exact ⟨u, by rw [hu]; abel⟩

theorem span_eq_top {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    (π : Module.End k W) (e r : ℕ) (hπ : π ^ e = 0) (x : Fin r → W)
    (hx : ∀ v : W, ∃ a ∈ Submodule.span k (Set.range x), ∃ u : W, v = a + π u) :
    Submodule.span k (Set.range fun q : Fin r × Fin e => (π ^ (q.2 : ℕ)) (x q.1)) = ⊤ := by
  classical
  set S := Submodule.span k (Set.range fun q : Fin r × Fin e => (π ^ (q.2 : ℕ)) (x q.1)) with hS
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    rw [pow_zero] at hπ
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : v = 0 := by simpa using LinearMap.congr_fun hπ v
    rw [hv]
    exact S.zero_mem
  have hinv : ∀ s ∈ S, π s ∈ S := by
    intro s hs
    refine Submodule.span_induction (p := fun s _ => π s ∈ S) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      by_cases hj : (j : ℕ) + 1 < e
      · apply Submodule.subset_span
        refine ⟨(i, ⟨(j : ℕ) + 1, hj⟩), ?_⟩
        simp [pow_succ', Module.End.mul_apply]
      · have hje : (j : ℕ) + 1 = e := by omega
        have h0 : π ((π ^ (j : ℕ)) (x i)) = 0 := by
          have h1 : (π ^ ((j : ℕ) + 1)) (x i) = π ((π ^ (j : ℕ)) (x i)) := by
            rw [pow_succ', Module.End.mul_apply]
          rw [← h1, hje, hπ, LinearMap.zero_apply]
        show π ((π ^ (j : ℕ)) (x i)) ∈ S
        rw [h0]
        exact S.zero_mem
    · simp
    · intro a c _ _ ha hc
      rw [map_add]
      exact S.add_mem ha hc
    · intro c a _ ha
      rw [map_smul]
      exact S.smul_mem c ha
  have hxS : ∀ a ∈ Submodule.span k (Set.range x), a ∈ S := by
    intro a ha
    refine Submodule.span_le.2 ?_ ha
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨(i, ⟨0, he⟩), by simp⟩
  have hpow : ∀ n : ℕ, ∀ s ∈ S, (π ^ n) s ∈ S := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih =>
      intro s hs
      rw [pow_succ', Module.End.mul_apply]
      exact hinv _ (ih s hs)
  have key : ∀ n : ℕ, ∀ v : W, ∃ s ∈ S, ∃ u : W, v = s + (π ^ n) u := by
    intro n
    induction n with
    | zero => intro v; exact ⟨0, S.zero_mem, v, by simp⟩
    | succ n ih =>
      intro v
      obtain ⟨s, hs, u, rfl⟩ := ih v
      obtain ⟨a, ha, u', rfl⟩ := hx u
      refine ⟨s + (π ^ n) a, S.add_mem hs (hpow n a (hxS a ha)), u', ?_⟩
      rw [map_add, pow_succ, Module.End.mul_apply, add_assoc]
  refine Submodule.eq_top_iff'.2 fun v => ?_
  obtain ⟨s, hs, u, rfl⟩ := key e v
  rw [hπ, LinearMap.zero_apply, add_zero]
  exact hs

end PositivityTheory.Xgn.JordanBasis
