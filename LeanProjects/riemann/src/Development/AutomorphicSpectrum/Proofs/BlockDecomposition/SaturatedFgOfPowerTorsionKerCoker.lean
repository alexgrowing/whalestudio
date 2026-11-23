import Mathlib

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat

theorem saturated_fg_of_powerTorsion_ker_coker :
    ∀ (B : Type) [CommRing B] (x : B) (M N : Type) [AddCommGroup M] [Module B M]
      [AddCommGroup N] [Module B N] (e : M →ₗ[B] N),
      (∀ m, e m = 0 → ∃ l : ℕ, x ^ l • m = 0) →
      (∀ f, ∃ (l : ℕ) (m : M), e m = x ^ l • f) →
      (∃ s : Finset N, ∀ f : N, ∃ k : ℕ, x ^ k • f ∈ Submodule.span B (s : Set N)) →
      ∃ T : Finset M, ∀ m : M, ∃ k : ℕ, x ^ k • m ∈ Submodule.span B (T : Set M) := by
  classical
  intro B _ x M N _ _ _ _ e hker hcoker hfg
  obtain ⟨s, hs⟩ := hfg
  choose l lift hlift using hcoker
  set L := ∑ n ∈ s, l n with hL
  have key : ∀ f ∈ Submodule.span B (s : Set N),
      ∃ t ∈ Submodule.span B ((s.image lift : Finset M) : Set M), e t = x ^ L • f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem n hn =>
      refine ⟨x ^ (L - l n) • lift n, Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem lift hn))), ?_⟩
      rw [map_smul, hlift, smul_smul, ← pow_add,
        Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hn)]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨ta, hta, ea⟩ := ha
      obtain ⟨tb, htb, eb⟩ := hb
      exact ⟨ta + tb, add_mem hta htb, by rw [map_add, ea, eb, smul_add]⟩
    | smul c a _ ha =>
      obtain ⟨t, ht, et⟩ := ha
      exact ⟨c • t, Submodule.smul_mem _ _ ht, by rw [map_smul, et, smul_comm]⟩
  refine ⟨s.image lift, fun m0 => ?_⟩
  obtain ⟨k, hk⟩ := hs (e m0)
  obtain ⟨t, ht, et⟩ := key _ hk
  have he : e (x ^ (L + k) • m0 - t) = 0 := by
    rw [map_sub, map_smul, et, smul_smul, ← pow_add, sub_self]
  obtain ⟨l', hl'⟩ := hker _ he
  refine ⟨l' + (L + k), ?_⟩
  have hm : x ^ (l' + (L + k)) • m0 = x ^ l' • t := by
    rw [smul_sub, smul_smul, ← pow_add, sub_eq_zero] at hl'
    exact hl'
  rw [hm]
  exact Submodule.smul_mem _ _ ht

end GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat
