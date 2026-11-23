import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

namespace GlobalTheory.CompanionTheory.TyFin

theorem intw_eq_invariants {Γ : Type} [Group Γ] {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) :
    Intw ρ σ = Representation.invariants (Representation.linHom ρ σ) := by
  ext φ
  rw [Representation.mem_invariants]
  constructor
  · intro h g
    have hg : φ ∘ₗ ρ g⁻¹ = σ g⁻¹ ∘ₗ φ := h g⁻¹
    rw [Representation.linHom_apply, hg]
    ext v
    simp [← Module.End.mul_apply, ← map_mul]
  · intro h g
    have hg := h g
    rw [Representation.linHom_apply] at hg
    ext v
    have := LinearMap.congr_fun hg (ρ g v)
    simpa [← Module.End.mul_apply, ← map_mul] using this.symm

theorem intwIp : ReciprocityTheory.Ty.Fin.St.IntwIp := by
  intro Γ _ _ V _ _ _ W _ _ _ ρ σ
  have hc : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have h := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom ρ σ)
  rw [intw_eq_invariants, ← h]
  simp [ip, Set.ncard_univ, Representation.char_linHom]

end GlobalTheory.CompanionTheory.TyFin
