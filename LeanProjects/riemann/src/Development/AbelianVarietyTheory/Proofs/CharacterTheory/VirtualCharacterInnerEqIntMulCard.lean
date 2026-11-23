import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingAddNatPosSymm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharacters
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInvStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

open Polynomial in
private lemma exists_nat_sum_mul_apply_inv_eq_mul_card (G : Type) [Group G] [Fintype G] (x y : G → ℂ)
    (hx : _root_.GlobalTheory.BI.IsChar ℂ ℂ x) (hy : _root_.GlobalTheory.BI.IsChar ℂ ℂ y) :
    ∃ n : ℕ, ∑ g, x g * y g⁻¹ = n * (Nat.card G : ℂ) := by
  obtain ⟨n, hn⟩ := (_root_.GlobalTheory.BI.pair_add_nat_pos_symm ℂ ℂ G).2.1 x y hx hy
  unfold _root_.GlobalTheory.BI.pair at hn
  rw [finsum_eq_sum_of_fintype] at hn
  have hc : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  refine ⟨n, ?_⟩
  rw [← hn, inv_mul_eq_div, div_mul_cancel₀ _ hc]

open Polynomial in

theorem _root_.GlobalTheory.BI.finsum_mul_star_virt_int : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ),
    a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G → b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G →
    ∃ m : ℤ, ∑ᶠ g, a g * star (b g) = m * (Nat.card G : ℂ) := by
  intro G _ _ a b ha hb
  haveI := Fintype.ofFinite G
  have hstar : ∀ g, star (b g) = b g⁻¹ := _root_.GlobalTheory.CuspGL.star_virt_eq_inv G b hb
  rw [finsum_eq_sum_of_fintype]
  simp_rw [hstar]
  obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub ℂ ℂ G a).mp ha
  obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub ℂ ℂ G b).mp hb
  obtain ⟨n₁₁, h₁₁⟩ := exists_nat_sum_mul_apply_inv_eq_mul_card G a₁ b₁ ha₁ hb₁
  obtain ⟨n₁₂, h₁₂⟩ := exists_nat_sum_mul_apply_inv_eq_mul_card G a₁ b₂ ha₁ hb₂
  obtain ⟨n₂₁, h₂₁⟩ := exists_nat_sum_mul_apply_inv_eq_mul_card G a₂ b₁ ha₂ hb₁
  obtain ⟨n₂₂, h₂₂⟩ := exists_nat_sum_mul_apply_inv_eq_mul_card G a₂ b₂ ha₂ hb₂
  refine ⟨n₁₁ - n₁₂ - n₂₁ + n₂₂, ?_⟩
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, h₁₁, h₁₂, h₂₁, h₂₂]
  push_cast
  ring

end GlobalTheory.BI
