import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open IsLocalRing

namespace GlobalTheory

theorem exists_mem_submonoid_dvd_mul_of_forall_height_eq_one :
    ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  intro B _ _ _ _ S _ x y hy h
  by_contra! hS
  set M := B ⧸ Ideal.span {y}
  set N : Submodule B M := B ∙ (Ideal.Quotient.mk (Ideal.span {y}) x)
  have hmem : ∀ r : B, r ∈ Module.annihilator B N ↔ y ∣ r * x := by
    intro r
    change r ∈ Submodule.annihilator N ↔ _
    rw [Submodule.mem_annihilator_span_singleton, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  set I := Module.annihilator B N
  have hdisj : Disjoint (S : Set B) (I : Set B) := by
    rw [Set.disjoint_left]
    intro u hu huI
    exact hS u hu ((hmem u).mp huI)
  obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint I S hdisj.symm
  obtain ⟨P', hP'min, hP'P⟩ := Ideal.exists_minimalPrimes_le hIP
  have hass : P' ∈ associatedPrimes B N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B N hP'min
  have hass' : P' ∈ associatedPrimes B M :=
    associatedPrimes.subset_of_injective Subtype.val_injective (f := N.subtype) hass
  obtain ⟨hpr, h1, hyP⟩ := (mem_associatedPrimes_iff_height_eq_one hy).mp hass'
  obtain ⟨t, htQ, ht⟩ := h P' hpr h1 hyP (hPS.symm.mono_right hP'P)
  exact htQ (hP'min.1.2 ((hmem t).mpr ht))

end GlobalTheory
