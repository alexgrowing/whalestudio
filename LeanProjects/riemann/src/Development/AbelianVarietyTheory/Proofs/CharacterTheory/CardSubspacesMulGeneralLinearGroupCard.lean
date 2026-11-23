import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesOfFinrankMulCardBasesStatement

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem card_GL_eq_prod_range (F : Type) [Field F] [Finite F] (n : ℕ) :
    Nat.card (GL (Fin n) F) = ∏ i ∈ Finset.range n, (Nat.card F ^ n - Nat.card F ^ i) := by
  classical
  haveI := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Nat.card_eq_fintype_card,
    ← Fin.prod_univ_eq_prod_range (fun i => Fintype.card F ^ n - Fintype.card F ^ i)]

theorem card_subspaces_mul_glCard : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * (Nat.card F : ℂ) ^ (a * (Module.finrank F V - a)) * glCard F a * glCard F (Module.finrank F V - a) = glCard F (Module.finrank F V) := by
  intro F _ _ V _ _ _ a ha
  have h := GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases F V a ha
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le ha
  have hb' : Module.finrank F V - a = b := by omega
  rw [hb']
  rw [hb] at h ⊢
  unfold glCard
  rw [card_GL_eq_prod_range, card_GL_eq_prod_range, card_GL_eq_prod_range]
  have key : Nat.card {W : Submodule F V // Module.finrank F W = a} * Nat.card F ^ (a * b) *
      (∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i)) *
      (∏ i ∈ Finset.range b, (Nat.card F ^ b - Nat.card F ^ i)) =
      ∏ i ∈ Finset.range (a + b), (Nat.card F ^ (a + b) - Nat.card F ^ i) := by
    rw [Finset.prod_range_add, ← h]
    have h2 : ∏ i ∈ Finset.range b, (Nat.card F ^ (a + b) - Nat.card F ^ (a + i)) =
        Nat.card F ^ (a * b) * ∏ i ∈ Finset.range b, (Nat.card F ^ b - Nat.card F ^ i) := by
      simp only [pow_add, ← Nat.mul_sub, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_range, pow_mul]
    rw [h2]
    ring
  exact_mod_cast key

end GlobalTheory.CuspGL
