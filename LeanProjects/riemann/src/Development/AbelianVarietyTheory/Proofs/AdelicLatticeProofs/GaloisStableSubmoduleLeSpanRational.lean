import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixedStatement

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.GaloisDescent

private theorem exists_rational_support_subset_of_galois_stable {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hw0 hcard
  have hrepr0 : b.repr w ≠ 0 := fun h => hw0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k₀, hk₀⟩ := Finsupp.support_nonempty_iff.mpr hrepr0
  have hk₀' : b.repr w k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀

  have hvW : (b.repr w k₀)⁻¹ • w ∈ W := W.smul_mem _ hw
  have hvk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w) k = (b.repr w k₀)⁻¹ * b.repr w k := by
    intro k; simp
  have hv1 : b.repr ((b.repr w k₀)⁻¹ • w) k₀ = 1 := by
    rw [hvk, inv_mul_cancel₀ hk₀']
  by_cases hfix : ∀ σ : ℂ ≃+* ℂ, ∀ k,
      σ (b.repr ((b.repr w k₀)⁻¹ • w) k) = b.repr ((b.repr w k₀)⁻¹ • w) k
  ·
    refine ⟨_, hvW, ?_, fun k => GlobalTheory.T.exists_rat_of_forall_complex_ringEquiv_fixed _ (fun σ => hfix σ k), ?_⟩
    · intro h0
      rw [h0, map_zero, Finsupp.zero_apply] at hv1
      exact zero_ne_one hv1
    · intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      rw [hvk] at hk
      exact right_ne_zero_of_mul hk
  ·
    push Not at hfix
    obtain ⟨σ, k₁, hk₁⟩ := hfix
    obtain ⟨v', hv'W, hv'⟩ := hW σ _ hvW
    have hdW : (b.repr w k₀)⁻¹ • w - v' ∈ W := W.sub_mem hvW hv'W
    have hdk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w - v') k =
        b.repr ((b.repr w k₀)⁻¹ • w) k - σ (b.repr ((b.repr w k₀)⁻¹ • w) k) := by
      intro k; rw [map_sub, Finsupp.sub_apply, hv']
    have hd0 : (b.repr w k₀)⁻¹ • w - v' ≠ 0 := by
      intro h
      have := hdk k₁
      rw [h, map_zero, Finsupp.zero_apply] at this
      exact hk₁ (sub_eq_zero.mp this.symm).symm
    have hsub : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support ⊆ (b.repr w).support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      intro hwk
      apply hk
      rw [hdk, hvk, hwk]
      simp
    have hk₀d : k₀ ∉ (b.repr ((b.repr w k₀)⁻¹ • w - v')).support := by
      rw [Finsupp.mem_support_iff, not_not, hdk, hv1, map_one, sub_self]
    have hlt : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support.card < n := by
      rw [← hcard]
      exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k₀, hk₀, hk₀d⟩)
    obtain ⟨u, huW, hu0, hurat, husub⟩ := ih _ hlt _ hdW hd0 rfl
    exact ⟨u, huW, hu0, hurat, husub.trans hsub⟩

theorem exists_rational_support_subset {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) (n : ℕ) :
    ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support :=
  fun w hw hw0 hcard => exists_rational_support_subset_of_galois_stable b W hW n w hw hw0 hcard

private theorem mem_span_rational_of_galois_stable_of_support_card {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, (b.repr w).support.card = n →
      w ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hcard
  by_cases hw0 : w = 0
  · rw [hw0]; exact Submodule.zero_mem _
  obtain ⟨u, huW, hu0, hurat, husub⟩ :=
    exists_rational_support_subset b W hW n w hw hw0 hcard
  have hru : b.repr u ≠ 0 := fun h => hu0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hru
  have huk : b.repr u k ≠ 0 := Finsupp.mem_support_iff.mp hk

  have hdk : ∀ j, b.repr (w - (b.repr w k / b.repr u k) • u) j =
      b.repr w j - (b.repr w k / b.repr u k) * b.repr u j := by
    intro j; simp
  have hsub : (b.repr (w - (b.repr w k / b.repr u k) • u)).support ⊆ (b.repr w).support := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj ⊢
    intro hwj
    apply hj
    have huj : b.repr u j = 0 := by
      by_contra h
      exact Finsupp.mem_support_iff.mp (husub (Finsupp.mem_support_iff.mpr h)) hwj
    rw [hdk, hwj, huj]
    simp
  have hkout : k ∉ (b.repr (w - (b.repr w k / b.repr u k) • u)).support := by
    rw [Finsupp.mem_support_iff, not_not, hdk, div_mul_cancel₀ _ huk, sub_self]
  have hlt : (b.repr (w - (b.repr w k / b.repr u k) • u)).support.card < n := by
    rw [← hcard]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k, husub hk, hkout⟩)
  have h1 := ih _ hlt _ (W.sub_mem hw (W.smul_mem _ huW)) rfl
  have h2 : u ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} :=
    Submodule.subset_span ⟨huW, hurat⟩
  have h3 := Submodule.add_mem _ h1 (Submodule.smul_mem _ (b.repr w k / b.repr u k) h2)
  rwa [sub_add_cancel] at h3

theorem le_span_rational :
    ∀ (V κ : Type) [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (W : Submodule ℂ V), (∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) → W ≤ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro V κ _ _ b W hW w hw
  exact mem_span_rational_of_galois_stable_of_support_card b W hW _ w hw rfl

end GlobalTheory.ClassFin.GaloisDescent
