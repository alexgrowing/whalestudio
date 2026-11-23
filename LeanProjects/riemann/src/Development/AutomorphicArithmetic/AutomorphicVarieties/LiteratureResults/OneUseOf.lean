import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd

namespace UpperTheory.V.Lit

def OneUse : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (ι : Qbar p ≃+* ℂ) (B : ℕ),
    ∃ k ≥ B, 0 < k ∧ p - 1 ∣ k ∧ ∃ (φ : TR.Sm F 2) (c₀ : (Af F)ˣ → ℂ) (c : Ideal (𝓞 F) → ℂ),
      IsHol k (fun _ => 0) 1 φ ∧ HasExp φ.1 k c₀ c ∧ (∀ y, ‖ι.symm (c₀ y) - 1‖ < 1) ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (c 𝔪)‖ < 1

theorem oneUse_of (h : Published.HilbertOne) : OneUse := by
  intro F _ _ _ p hp hl ι B
  obtain ⟨N, hN⟩ := h F p hl ι
  have hpos : 0 < (p - 1) * p ^ N := Nat.mul_pos (Nat.sub_pos_of_lt hp.out.one_lt) (pow_pos hp.out.pos N)
  exact ⟨(p - 1) * p ^ N * (B + 1), (Nat.le_succ B).trans (Nat.le_mul_of_pos_left _ hpos), Nat.mul_pos hpos B.succ_pos,
    (dvd_mul_right _ _).mul_right _, hN _ (Nat.mul_pos hpos B.succ_pos) (dvd_mul_right _ _)⟩

end UpperTheory.V.Lit
