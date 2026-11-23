import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationSubalgebraFracStatement
open IsLocalRing

namespace GlobalTheory

theorem localDecomp_core : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → (∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (W : μ → Subalgebra R (Localization.AtPrime Q)), Monotone W ∧ (∀ x : Localization.AtPrime Q, ∃ m, x ∈ W m) ∧ (∀ m, ∀ x ∈ W m, IsUnit x → ∃ z ∈ W m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W m)) := by
  intro R B _ _ _ Q _ ι _ _ _ C hC hcov hét hann
  have hV := fun i => GlobalTheory.T.exists_subalgebra_atPrime_fractions_equiv R B Q (C i) (hann i)
  choose V hVmem hVeq using hV
  refine ⟨ι, inferInstance, inferInstance, inferInstance, V, ?_, ?_, ?_, ?_⟩
  · intro i j hij x hx
    obtain ⟨a, ha, s, hs, hsQ, hxs⟩ := (hVmem i x).1 hx
    exact (hVmem j x).2 ⟨a, hC hij ha, s, hC hij hs, hsQ, hxs⟩
  · intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨i1, h1⟩ := hcov a
    obtain ⟨i2, h2⟩ := hcov (s : B)
    obtain ⟨k, hk1, hk2⟩ := directed_of (· ≤ ·) i1 i2
    exact ⟨k, (hVmem k _).2 ⟨a, hC hk1 h1, s, hC hk2 h2, s.2, IsLocalization.mk'_spec _ _ _⟩⟩
  · intro m x hx hu
    obtain ⟨a, ha, s, hs, hsQ, hxs⟩ := (hVmem m x).1 hx
    have hsu : IsUnit (algebraMap B (Localization.AtPrime Q) s) :=
      IsLocalization.map_units _ (⟨s, hsQ⟩ : Q.primeCompl)
    have hau : IsUnit (algebraMap B (Localization.AtPrime Q) a) := hxs ▸ hu.mul hsu
    have haQ : a ∉ Q := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q a).1 hau
    refine ⟨↑hu.unit⁻¹, (hVmem m _).2 ⟨s, hs, a, ha, haQ, ?_⟩, hu.mul_val_inv⟩
    calc (↑hu.unit⁻¹ : Localization.AtPrime Q) * algebraMap B _ a
        = ↑hu.unit⁻¹ * (x * algebraMap B _ s) := by rw [hxs]
      _ = algebraMap B _ s := by rw [← mul_assoc, hu.val_inv_mul, one_mul]
  · intro m
    obtain ⟨A, i1, i2, i3, q, i4, ⟨e⟩⟩ := hét m
    obtain ⟨f⟩ := hVeq m
    exact ⟨A, i1, i2, i3, q, i4, ⟨e.trans f⟩⟩

end GlobalTheory
