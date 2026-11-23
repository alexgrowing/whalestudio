import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo

set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine

theorem eq_zero_of_eval_real {σ : Type} (Q : MvPolynomial σ ℂ)
    (h : ∀ x : σ → ℝ, eval (fun i => (x i : ℂ)) Q = 0) : Q = 0 := by
  refine MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) ?_
  intro x hx
  have hx' : ∀ i, ∃ r : ℝ, (r : ℂ) = x i := fun i => hx i (Set.mem_univ i)
  choose r hr using hx'
  have : x = fun i => (r i : ℂ) := funext fun i => (hr i).symm
  rw [this, h, map_zero]

def hermSubst (ab : Fin 2 × Fin 2) : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  !![X (0, 0), X (0, 1) + C Complex.I * X (1, 0); X (0, 1) - C Complex.I * X (1, 0), X (1, 1)] ab.1 ab.2

theorem eval_bind_hermSubst (P : MvPolynomial (Fin 2 × Fin 2) ℂ) (x : Fin 2 × Fin 2 → ℂ) :
    eval x (bind₁ hermSubst P) =
      eval (entries !![x (0, 0), x (0, 1) + Complex.I * x (1, 0); x (0, 1) - Complex.I * x (1, 0), x (1, 1)]) P := by
  have h1 : (fun i => eval x (hermSubst i)) =
      entries !![x (0, 0), x (0, 1) + Complex.I * x (1, 0); x (0, 1) - Complex.I * x (1, 0), x (1, 1)] := by
    funext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [hermSubst, entries]
  rw [← h1]
  exact eval₂Hom_bind₁ (RingHom.id ℂ) x hermSubst P

theorem eq_zero_of_eval_hermitian (P : MvPolynomial (Fin 2 × Fin 2) ℂ)
    (h : ∀ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian → MvPolynomial.eval (entries H) P = 0) : P = 0 := by
  have hQ : bind₁ hermSubst P = 0 := by
    refine eq_zero_of_eval_real _ fun x => ?_
    rw [eval_bind_hermSubst]
    refine h _ ?_
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.conjTranspose_apply, sub_eq_add_neg]
  refine MvPolynomial.funext fun y => ?_
  have h2 := eval_bind_hermSubst P
    (entries !![y (0, 0), (y (0, 1) + y (1, 0)) / 2; (y (0, 1) - y (1, 0)) / (2 * Complex.I), y (1, 1)])
  rw [hQ] at h2
  rw [map_zero] at h2 ⊢
  rw [h2]
  congr 2
  funext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> simp [entries] <;> field_simp <;> ring

end GlobalTheory.FibLine
