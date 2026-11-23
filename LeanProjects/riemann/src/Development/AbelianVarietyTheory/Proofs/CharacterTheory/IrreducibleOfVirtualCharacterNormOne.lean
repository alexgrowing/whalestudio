import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterIrreducibleExpansionNormSqStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem finsupp_eq_single_of_sum_sq_eq_one {α : Type} (c : α →₀ ℤ)
    (h : (c.sum fun _ m => m ^ 2) = 1) :
    ∃ a, c.support = {a} ∧ (c a = 1 ∨ c a = -1) := by
  simp only [Finsupp.sum] at h
  have hge : ∀ b ∈ c.support, (1 : ℤ) ≤ c b ^ 2 := by
    intro b hb
    have hb' : c b ≠ 0 := Finsupp.mem_support_iff.mp hb
    rcases lt_or_gt_of_ne hb' with hlt | hgt <;> nlinarith
  have hle : (c.support.card : ℤ) ≤ 1 := by
    calc (c.support.card : ℤ) = ∑ _b ∈ c.support, (1 : ℤ) := by simp
      _ ≤ ∑ b ∈ c.support, c b ^ 2 := Finset.sum_le_sum hge
      _ = 1 := h
  have hne : c.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at h
    exact zero_ne_one h
  have hcard : c.support.card = 1 := by
    have := hne.card_pos
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, ha, ?_⟩
  rw [ha, Finset.sum_singleton] at h
  have h1 : c a ≤ 1 := by nlinarith
  have h2 : -1 ≤ c a := by nlinarith
  have h3 : c a ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  omega

private theorem exists_pos_nat_apply_one_of_isIrrChar {G : Type} [Group G] (χ : G → ℂ) (h : IsIrrChar ℂ ℂ χ) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = n := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  refine ⟨n, ?_, ?_⟩
  · have hs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
    have hnt : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · exfalso
      subst h0
      obtain ⟨x, y, hxy⟩ := hnt
      exact hxy (Subsingleton.elim (α := Fin 0 → ℂ) x y)
    · exact hn
  · rw [hχ, Representation.char_one]
    simp

theorem irr_of_norm_one : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∑ᶠ g, φ g * star (φ g) = (Nat.card G : ℂ) → (IsIrrChar ℂ ℂ φ ∨ IsIrrChar ℂ ℂ (-φ)) ∧ (IsChar ℂ ℂ φ → IsIrrChar ℂ ℂ φ ∧ ∃ n : ℕ, 0 < n ∧ φ 1 = n) := by
  intro G _ _ φ hφ hnorm
  obtain ⟨c, hirr, hsum, hsq⟩ := GlobalTheory.T.virtualCharacter_irreducible_expansion_normSq G φ hφ
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : (c.sum fun _ m => (m : ℂ) ^ 2) = 1 :=
    mul_right_cancel₀ hG ((hsq.symm.trans hnorm).trans (one_mul _).symm)
  have h2 : (c.sum fun _ m => m ^ 2) = 1 := by
    simp only [Finsupp.sum] at h1 ⊢
    exact_mod_cast h1
  obtain ⟨χ, hsupp, hc⟩ := finsupp_eq_single_of_sum_sq_eq_one c h2
  have hχ : IsIrrChar ℂ ℂ χ := hirr χ (by rw [hsupp]; exact Finset.mem_singleton_self χ)
  have hφχ : φ = c χ • χ := by
    rw [hsum, Finsupp.sum, hsupp, Finset.sum_singleton]
  have key : φ = χ ∨ φ = -χ := by
    rcases hc with h | h
    · left
      rw [hφχ, h, one_smul]
    · right
      rw [hφχ, h, neg_smul, one_smul]
  obtain ⟨n, hn, hn1⟩ := exists_pos_nat_apply_one_of_isIrrChar χ hχ
  rcases key with rfl | rfl
  · exact ⟨Or.inl hχ, fun _ => ⟨hχ, n, hn, hn1⟩⟩
  · refine ⟨Or.inr (by simpa using hχ), fun hc' => ?_⟩
    exfalso
    obtain ⟨-, -, m, hm, -⟩ := GlobalTheory.isChar_restrict_conj_one ℂ ℂ G (-χ) hc'
    have h3 : ((m + n : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hm, ← hn1, Pi.neg_apply]
      ring
    have h4 : m + n = 0 := by exact_mod_cast h3
    omega

end GlobalTheory.BI
