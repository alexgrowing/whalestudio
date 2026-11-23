import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory

theorem patOfPlaces : ∀ (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F), ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) → (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) := by
  intro F _ _ κ ρ s τ j R hR a b hab
  obtain ⟨h1, h2⟩ := hR
  have hA : ∀ (i : Fin j) (u : Fin τ), κ + (s + 1) + i.val * τ + u.val < κ + s + 1 + j * τ := by
    intro i u
    have hi : i.val + 1 ≤ j := i.2
    have hu := u.2
    have : (i.val + 1) * τ ≤ j * τ := Nat.mul_le_mul_right _ hi
    have e : (i.val + 1) * τ = i.val * τ + τ := by ring
    omega
  have hdiv : ∀ (i : Fin j) (u : Fin τ), (κ + (s + 1) + i.val * τ + u.val - (κ + s + 1)) / τ = i.val := by
    intro i u
    have hτ : 0 < τ := Nat.pos_of_ne_zero (fun h => by subst h; exact u.elim0)
    have e : κ + (s + 1) + i.val * τ + u.val - (κ + s + 1) = u.val + τ * i.val := by
      rw [Nat.mul_comm]; omega
    rw [e, Nat.add_mul_div_left _ _ hτ, Nat.div_eq_of_lt u.2, zero_add]
  rcases a with (i | i) | ⟨i, u⟩ <;> rcases b with (i' | i') | ⟨i', u'⟩
  ·
    simp only [FreeIx, FreeTop, not_lt, Fin.le_def] at hab
    simp only [zPos]
    by_cases h : i.val = i'.val
    · have : i = i' := Fin.ext h
      subst this
      rw [if_pos rfl]
      exact (h1 _ (by omega)).1
    · rw [if_neg (by intro e; simp only [Sum.inl.injEq] at e; exact h (congrArg Fin.val e))]
      refine (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inl ?_))
      simp only [symIdx]; split_ifs <;> omega
  ·
    simp only [FreeIx, FreeTop, not_lt] at hab
    simp only [zPos]
    rw [if_neg (by simp)]
    rcases Nat.lt_or_eq_of_le hab with hl | hl
    · refine (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inl ?_))
      simp only [symIdx]; split_ifs <;> omega
    · exact (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · simp [FreeIx] at hab
  ·
    simp only [FreeIx, FreeTop, not_lt] at hab
    simp only [zPos]
    rw [if_neg (by simp)]
    refine (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inl ?_))
    simp only [symIdx]; split_ifs <;> omega
  ·
    simp only [FreeIx, FreeTop, not_lt, Fin.le_def] at hab
    simp only [zPos]
    by_cases h : i.val = i'.val
    · have : i = i' := Fin.ext h
      subst this
      rw [if_pos rfl]
      exact (h1 _ (by omega)).1
    · rw [if_neg (by intro e; simp only [Sum.inl.injEq, Sum.inr.injEq] at e; exact h (congrArg Fin.val e))]
      refine (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inl ?_))
      simp only [symIdx]; split_ifs <;> omega
  · simp [FreeIx] at hab
  ·
    simp only [zPos]
    rw [if_neg (by simp)]
    have := hA i u
    exact (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inl (by omega))
  · simp only [zPos]
    rw [if_neg (by simp)]
    have := hA i u
    exact (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inl (by omega))
  ·
    simp only [FreeIx, not_le, Fin.lt_def] at hab
    simp only [zPos]
    rw [if_neg (by intro e; simp only [Sum.inr.injEq, Prod.mk.injEq] at e; rw [e.1] at hab; omega)]
    have hu := hA i u
    have hu' := hA i' u'
    apply h2 _ _ (by omega) (by omega) (by omega)
    rw [hdiv, hdiv]
    exact hab

end GlobalTheory
