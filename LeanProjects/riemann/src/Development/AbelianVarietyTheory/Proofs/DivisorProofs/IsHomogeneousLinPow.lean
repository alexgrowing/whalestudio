import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ArInt GlobalTheory.CovTest

namespace GlobalTheory.SwapTrue

variable {ι : Type} {N j : ℕ}

theorem block_lt (hj : j ≤ N) (z : Σ a : ι × Bool, Fin (rkB ι N j a)) : cond z.1.2 0 j + (z.2 : ℕ) < N := by
  obtain ⟨⟨τ, b⟩, i⟩ := z
  have hi := i.2
  cases b <;> simp only [rkB, cond_true, cond_false] at hi ⊢ <;> omega

def blockEquiv (ι : Type) (N j : ℕ) (hj : j ≤ N) : (Σ a : ι × Bool, Fin (rkB ι N j a)) ≃ ι × Fin N where
  toFun z := (z.1.1, ⟨cond z.1.2 0 j + z.2, block_lt hj z⟩)
  invFun x := if h : (x.2 : ℕ) < j then ⟨(x.1, true), ⟨x.2, by simpa [rkB] using h⟩⟩
    else ⟨(x.1, false), ⟨x.2 - j, by have := x.2.2; simp only [rkB, cond_false]; omega⟩⟩
  left_inv z := by
    obtain ⟨⟨τ, b⟩, i⟩ := z
    have hi := i.2
    cases b
    · simp only [rkB, cond_false] at hi
      have h : ¬ (j + (i : ℕ) < j) := by omega
      simp only [cond_false, h, dite_false]
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (by simp)))
    · simp only [rkB, cond_true] at hi
      have h : (0 + (i : ℕ) < j) := by omega
      simp only [cond_true, h, dite_true]
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (by simp)))
  right_inv x := by
    obtain ⟨τ, k⟩ := x
    dsimp only
    by_cases h : (k : ℕ) < j
    · rw [dif_pos h]
      exact Prod.ext rfl (Fin.ext (by simp))
    · rw [dif_neg h]
      exact Prod.ext rfl (Fin.ext (by simp; omega))

@[simp] theorem blockEquiv_fst (hj : j ≤ N) (z : Σ a : ι × Bool, Fin (rkB ι N j a)) :
    (blockEquiv ι N j hj z).1 = z.1.1 := rfl

@[simp] theorem blockEquiv_snd (hj : j ≤ N) (z : Σ a : ι × Bool, Fin (rkB ι N j a)) :
    ((blockEquiv ι N j hj z).2 : ℕ) = cond z.1.2 0 j + z.2 := rfl

theorem rename_lin_comp {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) (f : ι → ℝ) :
    rename e (lin fun z => f (e z)) = lin f := by
  simp only [lin, map_sum, map_mul, rename_C, rename_X]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

theorem isHomogeneous_lin_pow {κ : Type} [Fintype κ] (f : κ → ℝ) (d : ℕ) : ((lin f) ^ d).IsHomogeneous d := by
  have h : (lin f).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (f i) i
  simpa using h.pow d

open Classical in

theorem rename_swapPol {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ)
    (D : ℕ) (x y : κ) (n : ι → ℤ) :
    rename e (swapPol G D x y fun z => n (e z)) = swapPol G D (e x) (e y) n := by
  unfold swapPol
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  fin_cases i
  · simp
  · simp
  · show rename e (lin fun z => if z = x ∨ z = y then 0 else ((n (e z) : ℤ) : ℝ)) =
      lin fun z => if z = e x ∨ z = e y then 0 else (n z : ℝ)
    rw [← rename_lin_comp e]
    congr 2
    funext z
    simp only [e.injective.eq_iff]

open GlobalTheory.FlagPoly in

theorem swapAt_eq_swap [DecidableEq ι] (τ : ι) (a b : Fin N) : swapAt τ a b = ⇑(Equiv.swap (τ, a) (τ, b)) := by
  funext x
  obtain ⟨τ', k⟩ := x
  by_cases h : τ' = τ
  · subst h
    simp only [swapAt, if_true, Equiv.swap_apply_def, Prod.mk.injEq, true_and]
    split_ifs <;> rfl
  · simp [swapAt, h, Equiv.swap_apply_def]

theorem exists_adj (hj : j ≤ N) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) (hb : (b : ℕ) ≠ j) :
    ∃ (A : ι × Bool) (i i' : Fin (rkB ι N j A)), (i' : ℕ) = i + 1 ∧
      blockEquiv ι N j hj ⟨A, i⟩ = (τ, a) ∧ blockEquiv ι N j hj ⟨A, i'⟩ = (τ, b) := by
  have ha := a.2
  have hb' := b.2
  by_cases h : (a : ℕ) < j
  · have h' : (b : ℕ) < j := by omega
    refine ⟨(τ, true), ⟨a, by simpa [rkB] using h⟩, ⟨b, by simpa [rkB] using h'⟩, hab, ?_, ?_⟩ <;>
      exact Prod.ext rfl (Fin.ext (by simp))
  · refine ⟨(τ, false), ⟨a - j, by simp only [rkB, cond_false]; omega⟩, ⟨b - j, by simp only [rkB, cond_false]; omega⟩,
      by simp; omega, ?_, ?_⟩ <;> exact Prod.ext rfl (Fin.ext (by simp; omega))

open GlobalTheory.FlagPoly in

theorem swapAt_comp_equiv {κ : Type} {inst : DecidableEq κ} [DecidableEq ι] (e : κ ≃ ι × Fin N) (p q : κ) (τ : ι)
    (a b : Fin N) (hp : e p = (τ, a)) (hq : e q = (τ, b)) (z : κ) : swapAt τ a b (e z) = e (Equiv.swap p q z) := by
  rw [swapAt_eq_swap, ← hp, ← hq, Equiv.swap_apply_def, Equiv.swap_apply_def]
  simp only [e.injective.eq_iff]
  split_ifs <;> rfl

end GlobalTheory.SwapTrue
