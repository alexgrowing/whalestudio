import Mathlib
import Formalism.PadicSubsetSums.StableGradedCounts.FixedByAutomorphismInField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivAddOne

open Polynomial

namespace GlobalTheory.FixedRoots

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental k c) :
    ∃ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) ∧ σ c = c + 1 := by
  first
  | exact @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | (apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one ..)

theorem mem_of_forall_ringEquiv_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (k : Subfield Ω) (c : Ω) (hfix : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → σ c = c) : c ∈ k := by
  by_cases hc : Transcendental k c
  · exfalso
    obtain ⟨σ, hσk, hσc⟩ := exists_ringEquiv_add_one k c hc
    have := hfix σ hσk
    rw [hσc] at this
    simp at this
  · have hcA : IsAlgebraic k c := by simpa [Transcendental] using hc
    have hzA : c ∈ algebraicClosure k Ω := (mem_algebraicClosure_iff).2 hcA
    have : IsGalois k (algebraicClosure k Ω) := inferInstance
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by
        intro σ₀
        obtain ⟨σ, hσ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀
        apply Subtype.ext
        rw [← hσ]
        exact hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))
    have : ((r : k) : Ω) = c := congrArg Subtype.val hr
    rw [← this]
    exact r.2

theorem coeff_prod_mem {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω)
    (S : Finset Ω) (hS : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) (n : ℕ) :
    (∏ x ∈ S, (X - C x)).coeff n ∈ k := by
  apply mem_of_forall_ringEquiv_fixed k
  intro σ hσ
  have hmap : S.map σ.toEquiv.toEmbedding = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
      exact hS σ hσ x hx
    · simp
  have hP : (∏ x ∈ S, (X - C x)).map (σ : Ω →+* Ω) = ∏ x ∈ S, (X - C x) := by
    rw [Polynomial.map_prod]
    conv_rhs => rw [← hmap]
    rw [Finset.prod_map]
    simp
  have := congrArg (fun P => Polynomial.coeff P n) hP
  simpa [Polynomial.coeff_map] using this

theorem main : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω) (S : Finset Ω),
    (∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) → ∀ n,
      (∏ x ∈ S, (X - C x)).coeff n ∈ k :=
  fun _ _ _ _ k S hS n => coeff_prod_mem k S hS n

end GlobalTheory.FixedRoots
