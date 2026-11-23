import Mathlib
open scoped Classical

namespace GlobalTheory

theorem finsum_ite_eq_of_equiv {A B : Type} (PA : A → Prop) (PB : B → Prop)
    (e : {a // PA a} ≃ {b // PB b}) (g : A → ℂ) (h : B → ℂ)
    (hgh : ∀ a, h (e a).1 = g a.1) :
    (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ b, if PB b then h b else 0 := by
  have hA : (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ a : {a // PA a}, g a.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun a => (finsum_eq_if).symm
  have hB : (∑ᶠ b, if PB b then h b else 0) = ∑ᶠ b : {b // PB b}, h b.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun b => (finsum_eq_if).symm
  rw [hA, hB, ← finsum_comp_equiv e]
  exact finsum_congr fun a => (hgh a).symm

example : ∀ {A B : Type} (PA : A → Prop) (PB : B → Prop) (e : {a // PA a} ≃ {b // PB b}) (g : A → ℂ) (h : B → ℂ), (∀ a, h (e a).1 = g a.1) → (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ b, if PB b then h b else 0 :=
  fun PA PB e g h hgh => finsum_ite_eq_of_equiv PA PB e g h hgh

end GlobalTheory
