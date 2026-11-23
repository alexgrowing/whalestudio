import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem character_pairing_eq_finrank_hom (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K]
    (G : Type) [Group G] [Finite G] {n m : ℕ} (ρ : Representation K G (Fin n → K))
    (σ : Representation K G (Fin m → K)) :
    pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g))
      = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hK := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  rw [map_natCast] at hK
  rw [← hK]
  simp only [pair, finsum_eq_sum_of_fintype, map_mul, map_inv₀, map_natCast, map_sum]

theorem pair_add_nat_pos_symm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ a b c : G → L, pair (a + b) c = pair a c + pair b c) ∧ (∀ a b : G → L, IsChar K L a → IsChar K L b → ∃ n : ℕ, pair a b = (n : L)) ∧ (∀ φ : G → L, IsIrrChar K L φ → ∃ n : ℕ, 0 < n ∧ pair φ φ = (n : L)) ∧ ∀ a b : G → L, pair a b = pair b a := by
  intro K L _ _ _ _ _ G _ _
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c
    simp only [pair, finsum_eq_sum_of_fintype, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      mul_add]
  · rintro a b ⟨n, ρ, hρ⟩ ⟨m, σ, hσ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap σ ρ), ?_⟩
    rw [show a = fun g => algebraMap K L (ρ.character g) from funext hρ,
      show b = fun g => algebraMap K L (σ.character g) from funext hσ]
    exact character_pairing_eq_finrank_hom K L G σ ρ
  · rintro φ ⟨n, ρ, hirr, hρ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap ρ ρ), ?_, ?_⟩
    · have : IsSimpleModule (MonoidAlgebra K G) ρ.asModule :=
        (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
      have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra K G) _
      obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v ≠ 0 := exists_ne (0 : ρ.asModule)
      have : Nontrivial (Representation.IntertwiningMap ρ ρ) :=
        ⟨⟨Representation.IntertwiningMap.id ρ, 0, fun h => hv (by
          have hv0 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
          rwa [Representation.IntertwiningMap.id_apply, Representation.IntertwiningMap.coe_zero,
            Pi.zero_apply] at hv0)⟩⟩
      have : Module.Finite K (Representation.IntertwiningMap ρ ρ) :=
        Module.Finite.equiv (Representation.invariantsEquivIntertwiningMap ρ ρ)
      exact Module.finrank_pos
    · rw [show φ = fun g => algebraMap K L (ρ.character g) from funext hρ]
      exact character_pairing_eq_finrank_hom K L G ρ ρ
  · intro a b
    simp only [pair, finsum_eq_sum_of_fintype]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp [mul_comm])
end GlobalTheory.BI
