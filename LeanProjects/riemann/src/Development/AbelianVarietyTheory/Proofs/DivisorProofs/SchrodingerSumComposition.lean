import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped Matrix
open Matrix

namespace GlobalTheory

theorem schr_factor_data {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    {a b c : (κ → R) × (κ → R)}
    (h : ∀ φ : (κ → R) → ℂ, GlobalTheory.WeilM.schr ψ a φ = GlobalTheory.WeilM.schr ψ b (GlobalTheory.WeilM.schr ψ c φ)) :
    a.1 = b.1 + c.1 ∧ ∀ x : κ → R, ψ (x ⬝ᵥ a.2 + ⅟(2 : R) * (a.1 ⬝ᵥ a.2)) =
      ψ (x ⬝ᵥ b.2 + ⅟(2 : R) * (b.1 ⬝ᵥ b.2)) * ψ ((x + b.1) ⬝ᵥ c.2 + ⅟(2 : R) * (c.1 ⬝ᵥ c.2)) := by
  classical
  have hψne : ∀ v, ψ v ≠ 0 := fun v hv => by
    have h1 := AddChar.map_add_eq_mul ψ v (-v)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, hv, zero_mul] at h1
    exact one_ne_zero h1
  refine ⟨?_, fun x => ?_⟩
  · by_contra hne
    have hne' : b.1 + c.1 ≠ a.1 := fun e => hne e.symm
    have h0 := congrFun (h fun v => if v = a.1 then 1 else 0) 0
    simp only [GlobalTheory.WeilM.schr, zero_add, if_pos rfl, if_true, if_neg hne', mul_zero, mul_one] at h0
    exact hψne _ h0
  · have h1 := congrFun (h fun _ => 1) x
    simp only [GlobalTheory.WeilM.schr, mul_one] at h1
    exact h1

theorem schr_block_factor : ∀ {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b c a' b' c' : (κ → R) × (κ → R)),
    (∀ φ : (κ → R) → ℂ, GlobalTheory.WeilM.schr ψ a φ = GlobalTheory.WeilM.schr ψ b (GlobalTheory.WeilM.schr ψ c φ)) →
    (∀ φ : (κ → R) → ℂ, GlobalTheory.WeilM.schr ψ a' φ = GlobalTheory.WeilM.schr ψ b' (GlobalTheory.WeilM.schr ψ c' φ)) →
    ∀ Φ : (κ ⊕ κ → R) → ℂ,
      GlobalTheory.WeilM.schr ψ (Sum.elim a.1 a'.1, Sum.elim a.2 (-a'.2)) Φ =
        GlobalTheory.WeilM.schr ψ (Sum.elim b.1 0, Sum.elim b.2 0)
          (GlobalTheory.WeilM.schr ψ (Sum.elim 0 b'.1, Sum.elim 0 (-b'.2))
            (GlobalTheory.WeilM.schr ψ (Sum.elim c.1 c'.1, Sum.elim c.2 (-c'.2)) Φ)) := by
  intro R _ _ ψ κ _ a b c a' b' c' h h' Φ
  obtain ⟨ha1, hE⟩ := schr_factor_data ψ h
  obtain ⟨ha1', hE'⟩ := schr_factor_data ψ h'
  funext X
  obtain ⟨x, x', rfl⟩ : ∃ x x' : κ → R, X = Sum.elim x x' := ⟨_, _, (Sum.elim_comp_inl_inr X).symm⟩
  simp only [GlobalTheory.WeilM.schr, ← Sum.elim_add_add, sumElim_dotProduct_sumElim, dotProduct_neg, neg_dotProduct,
    dotProduct_zero, zero_dotProduct, add_zero, zero_add]
  have hP : Sum.elim (x + a.1) (x' + a'.1) = Sum.elim (x + b.1 + c.1) (x' + b'.1 + c'.1) := by
    rw [ha1, ha1', add_assoc, add_assoc]
  rw [hP]
  simp only [← mul_assoc]
  congr 1
  have hN : ∀ u v w : R, ψ u = ψ v * ψ w → ψ (-u) = ψ (-v) * ψ (-w) := fun u v w e => by
    rw [AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, e, mul_inv]
  have e1 := hE x
  have e2 := hN _ _ _ (hE' x')
  rw [show x ⬝ᵥ a.2 + -(x' ⬝ᵥ a'.2) + ⅟(2 : R) * (a.1 ⬝ᵥ a.2 + -(a'.1 ⬝ᵥ a'.2))
      = (x ⬝ᵥ a.2 + ⅟(2 : R) * (a.1 ⬝ᵥ a.2)) + -(x' ⬝ᵥ a'.2 + ⅟(2 : R) * (a'.1 ⬝ᵥ a'.2)) by ring,
    AddChar.map_add_eq_mul, e1, e2]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  ring

end GlobalTheory
