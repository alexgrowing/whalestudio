import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

theorem neg_inv_SL (a : SL(2, ℤ)) : (-a)⁻¹ = -a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [neg_mul_neg, mul_inv_cancel]

def pmSub (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Γ ∨ -g ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Γ.mul_mem ha hb)
    · exact Or.inr (by simpa only [mul_neg] using Γ.mul_mem ha hb)
    · exact Or.inr (by simpa only [neg_mul] using Γ.mul_mem ha hb)
    · exact Or.inl (by simpa only [neg_mul_neg] using Γ.mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Γ.inv_mem ha)
    · refine Or.inr ?_
      have := Γ.inv_mem ha
      rwa [neg_inv_SL] at this

theorem mem_pmSub {Γ : Subgroup SL(2, ℤ)} {g : SL(2, ℤ)} : g ∈ pmSub Γ ↔ g ∈ Γ ∨ -g ∈ Γ := by
  rfl

theorem le_pmSub (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pmSub Γ := by
  intro g hg
  exact Or.inl hg

theorem relIndex_pmSub {Γ : Subgroup SL(2, ℤ)} (hm : (-1 : SL(2, ℤ)) ∉ Γ) : Γ.relIndex (pmSub Γ) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨-1, mem_pmSub.2 (Or.inr (by rw [neg_neg]; exact Γ.one_mem)), fun b hb => ?_⟩
  rw [mul_neg_one]
  rcases mem_pmSub.1 hb with h | h
  · refine Or.inr ⟨h, fun h' => hm ?_⟩
    have := Γ.mul_mem (Γ.inv_mem h) h'
    rwa [mul_neg, inv_mul_cancel] at this
  · refine Or.inl ⟨h, fun h' => hm ?_⟩
    have := Γ.mul_mem (Γ.inv_mem h') h
    rwa [mul_neg, inv_mul_cancel] at this

theorem reps_index : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → (-1 : SL(2, ℤ)) ∉ Γ →
    ∃ (r : ℕ) (s : Fin r → SL(2, ℤ)), IsReps Γ s ∧ 2 * r = Γ.index := by
  intro Γ hΓ hm
  have : (pmSub Γ).FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSub Γ)
  let e : Fin (Nat.card (SL(2, ℤ) ⧸ pmSub Γ)) ≃ SL(2, ℤ) ⧸ pmSub Γ :=
    (Finite.equivFin (SL(2, ℤ) ⧸ pmSub Γ)).symm
  refine ⟨Nat.card (SL(2, ℤ) ⧸ pmSub Γ), fun i => (Quotient.out (e i))⁻¹, ⟨fun x => ?_, ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := e.surjective (QuotientGroup.mk x⁻¹)
    have hq : (QuotientGroup.mk (Quotient.out (e i)) : SL(2, ℤ) ⧸ pmSub Γ) = QuotientGroup.mk x⁻¹ := by
      rw [hi]; exact QuotientGroup.out_eq' _
    have hp := QuotientGroup.eq.1 hq
    have hx : x = ((Quotient.out (e i))⁻¹ * x⁻¹)⁻¹ * (Quotient.out (e i))⁻¹ := by group
    refine ⟨i, ?_⟩
    rcases mem_pmSub.1 ((pmSub Γ).inv_mem hp) with h | h
    · exact ⟨_, h, Or.inl hx⟩
    · refine ⟨_, h, Or.inr ?_⟩
      rw [neg_mul, neg_neg]
      exact hx
  · intro i j γ hγ hij
    dsimp only at hij
    have hp : ∃ p ∈ pmSub Γ, (Quotient.out (e i))⁻¹ = p * (Quotient.out (e j))⁻¹ := by
      rcases hij with h | h
      · exact ⟨γ, le_pmSub Γ hγ, h⟩
      · refine ⟨-γ, mem_pmSub.2 (Or.inr (by rw [neg_neg]; exact hγ)), ?_⟩
        rw [h, neg_mul]
    obtain ⟨p, hpP, hpe⟩ := hp
    have hmem : (Quotient.out (e j))⁻¹ * Quotient.out (e i) ∈ pmSub Γ := by
      have : (Quotient.out (e j))⁻¹ * Quotient.out (e i) = p⁻¹ := by
        have hi : Quotient.out (e i) = Quotient.out (e j) * p⁻¹ := by
          rw [← inv_inv (Quotient.out (e i)), hpe, mul_inv_rev, inv_inv]
        rw [hi, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact (pmSub Γ).inv_mem hpP
    have hq := QuotientGroup.eq.2 hmem
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at hq
    exact e.injective hq.symm
  · rw [← Subgroup.relIndex_mul_index (le_pmSub Γ), relIndex_pmSub hm]
    rfl

end GlobalTheory.OddFrame
