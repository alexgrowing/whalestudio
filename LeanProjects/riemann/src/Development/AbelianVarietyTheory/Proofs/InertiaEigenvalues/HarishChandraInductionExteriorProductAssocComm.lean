import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicProductExtendedByZeroAssoc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlipSimilar

noncomputable section

namespace GlobalTheory.GLq.HcRing

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem toG_val {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dif_pos x.isUnit]
  exact Units.ext rfl

theorem br_zero {a : ℕ} (M : Mt g a) : br 0 a M = M := by
  funext i j
  simp only [br, entN, zero_add, i.isLt, j.isLt, and_self, dif_pos]

theorem tl_self {a : ℕ} (M : Mt g a) : tl a M = M := by
  funext i j
  simp only [tl, entN, i.isLt, j.isLt, and_self, dif_pos]

theorem inPar_zero {n : ℕ} (M : Mt g n) : InPar 0 M := fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem inPar_self {a : ℕ} (M : Mt g a) : InPar a M := fun i _ _ hi => absurd i.isLt (not_lt.2 hi)

theorem class_conj {G : Type} [Group G] {χ : G → ℂ} (h : IsClass χ) (x y : G) : χ (y⁻¹ * x * y) = χ x := by
  have := h x y⁻¹
  rwa [inv_inv] at this

theorem mean_class {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsClass χ) (x : G) :
    (Fintype.card G : ℂ)⁻¹ * ∑ y : G, χ (y⁻¹ * x * y) = χ x := by
  simp only [class_conj h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

theorem hc_one_left (a : ℕ) (α : Gn g a → ℂ) (hα : IsClass α) : hc 0 a (fun _ => 1) α a = α := by
  funext x
  unfold hc hcT
  simp only [inPar_zero, if_true, one_mul,
    br_zero, toG_val]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ]
  exact mean_class hα x

theorem hc_one_right (a : ℕ) (α : Gn g a → ℂ) (hα : IsClass α) : hc a 0 α (fun _ => 1) a = α := by
  funext x
  unfold hc hcT
  simp only [inPar_self, if_true, mul_one,
    tl_self, toG_val]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ]
  exact mean_class hα x

theorem main : ∀ (g : ℕ) [Fact g.Prime] (a b c n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (γ : Gn g c → ℂ),
    IsClass α → IsClass β → IsClass γ →
      (n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n) ∧
      (n = a + b → hc a b α β n = hc b a β α n) ∧
      (hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α) :=
  fun g _ a b c n α β γ hα hβ hγ =>
    ⟨GlobalTheory.GLm.HcAssoc.hc_assoc g a b c n α β γ hα hβ hγ, GlobalTheory.HCComm.main g a b n α β hα hβ,
      hc_one_left a α hα, hc_one_right a α hα⟩

end GlobalTheory.GLq.HcRing
