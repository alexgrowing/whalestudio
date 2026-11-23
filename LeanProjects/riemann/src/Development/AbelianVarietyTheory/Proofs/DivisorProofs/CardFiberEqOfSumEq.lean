import Mathlib

open Polynomial

namespace GlobalTheory.CharDeg

theorem card_fiber_eq_of_sum_eq {M : Type} [Monoid M] {n : ℕ} (f g : Fin n → (M →* ℂ))
    (h : ∀ x, ∑ j, f j x = ∑ j, g j x) (ψ : M →* ℂ) :
    Nat.card {j // f j = ψ} = Nat.card {j // g j = ψ} := by
  classical
  have hli := linearIndependent_monoidHom M ℂ
  set s : Finset (M →* ℂ) := Finset.univ.image f ∪ Finset.univ.image g ∪ {ψ} with hs
  have key : ∀ u : Fin n → (M →* ℂ), (∀ j, u j ∈ s) →
      ∑ φ ∈ s, ((Finset.univ.filter fun j => u j = φ).card : ℂ) • (φ : M → ℂ) = ∑ j, (u j : M → ℂ) := by
    intro u hu
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := s) (g := u) (fun j _ => hu j)
      (fun j => (u j : M → ℂ))]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have hc : ∑ j ∈ Finset.univ.filter (fun j => u j = φ), (u j : M → ℂ)
        = ∑ j ∈ Finset.univ.filter (fun j => u j = φ), (φ : M → ℂ) :=
      Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
    rw [hc, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hzero : ∑ φ ∈ s, (((Finset.univ.filter fun j => f j = φ).card : ℂ)
      - ((Finset.univ.filter fun j => g j = φ).card : ℂ)) • (φ : M → ℂ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [key f (fun j => by simp [hs]), key g (fun j => by simp [hs]), sub_eq_zero]
    funext x
    simp [Finset.sum_apply, h x]
  have hψ := linearIndependent_iff'.mp hli s _ hzero ψ (by simp [hs])
  rw [sub_eq_zero, Nat.cast_inj] at hψ
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using hψ

def posMonoid {Λ : Type} [CommGroup Λ] (d : Λ →* Multiplicative ℤ) : Submonoid Λ where
  carrier := {x | x = 1 ∨ 0 < Multiplicative.toAdd (d x)}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · left; simp
    · right; simpa using hb
    · right; simpa using ha
    · right; simp only [map_mul, toAdd_mul]; omega

noncomputable def res {Λ : Type} [CommGroup Λ] (d : Λ →* Multiplicative ℤ) (χ : Λ →* ℂˣ) :
    posMonoid d →* ℂ :=
  (Units.coeHom ℂ).comp (χ.comp (posMonoid d).subtype)

theorem sum_eq_of_prod_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : ∏ j, (X - C (a j)) = ∏ j, (X - C (b j))) : ∑ j, a j = ∑ j, b j := by
  have := congrArg Polynomial.nextCoeff h
  rw [Polynomial.prod_X_sub_C_nextCoeff, Polynomial.prod_X_sub_C_nextCoeff] at this
  exact neg_inj.mp this

end GlobalTheory.CharDeg
