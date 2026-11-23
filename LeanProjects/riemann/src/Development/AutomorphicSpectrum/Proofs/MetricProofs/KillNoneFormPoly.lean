import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial

theorem killNone_formPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) :
    aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) (formPoly n a)
      = formPoly n fun w => a fun j => some (w j) := by
  classical
  unfold formPoly
  rw [map_sum]
  symm
  refine Finset.sum_of_injOn (fun (w : Fin n → σ) j => some (w j)) ?_ ?_ ?_ ?_
  · intro w _ w' _ h
    funext j
    exact Option.some_injective _ (congrFun h j)
  · intro w _
    exact Finset.mem_univ _
  · intro w _ hw
    have : ∃ j, w j = none := by
      by_contra hc
      apply hw
      have hc' : ∀ j, (w j).isSome := fun j => by
        cases h : w j with
        | none => exact absurd ⟨j, h⟩ hc
        | some _ => rfl
      exact ⟨fun j => (w j).get (hc' j), Finset.mem_coe.2 (Finset.mem_univ _), by funext j; simp⟩
    obtain ⟨j, hj⟩ := this
    rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro w _
    simp [map_prod]

theorem killNone_toWtS {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) :
    aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) (toWtS Q)
      = toWt (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) Q) := by
  have h : (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X)).comp toWtS
      = toWt.comp (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X)) := by
    apply MvPolynomial.algHom_ext
    intro o
    cases o with
    | none => simp [toWtS, toWt]
    | some p =>
      simp only [toWtS, toWt, AlgHom.comp_apply, aeval_X, Option.elim_some, aeval_rename]
      have : ((fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) ∘ some) = X := rfl
      rw [this, aeval_X_left_apply]
  exact DFunLike.congr_fun h Q

theorem eval_toWt_gap {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Ψ × Fin N) ℝ) (lam : Ψ × Fin N → ℝ) :
    eval lam (toWt Q) = eval (gap lam) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [toWt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [toWt, gap]

theorem eval_toWtS_gapS {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (lam : Ψ × Fin N → ℝ)
    (s : ℝ) : eval (fun o => o.elim s lam) (toWtS Q) = eval (gapS lam s) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [toWtS]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    cases i with
    | none => simp [toWtS, gapS]
    | some q =>
      simp only [toWtS, gapS, gap, aeval_X, eval_X, Option.elim_some, eval_rename]
      rfl

theorem poly_s_zero : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ),
    (∀ (a : (Fin n → Option (Ψ × Fin N)) → ℝ),
      aeval (fun o : Option (Ψ × Fin N) => o.elim 0 X) (toWtS (formPoly n a))
        = toWt (formPoly n fun w => a fun j => some (w j))) ∧
    (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (lam : Ψ × Fin N → ℝ), eval lam (toWt Q) = eval (gap lam) Q) ∧
    ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (lam : Ψ × Fin N → ℝ) (s : ℝ),
      eval (fun o => o.elim s lam) (toWtS Q) = eval (gapS lam s) Q := by
  intro Ψ _ N n
  refine ⟨fun a => ?_, eval_toWt_gap, eval_toWtS_gapS⟩
  rw [killNone_toWtS, killNone_formPoly]

end GlobalTheory.CompanionTheory.Ar.PB
