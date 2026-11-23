import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

private theorem lin_entry {d D : ℕ} (φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin D) :
    φ A i j = ∑ k, ∑ l, φ (Matrix.single k l 1) i j * A k l := by
  have e : A = ∑ k, ∑ l, A k l • Matrix.single k l (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [e]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem UpperTheory.window_linear_entry_estimate :
    ∀ (E : Type) [Field E] [NumberField E] (a d D : ℕ) (φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (M : GL (Fin a) (Cinf E) → Matrix (Fin d) (Fin d) ℂ), IsReg M → IsReg (fun y => φ (M y)) ∧ ∀ τ i j, eOf (fun y => φ (M y)) τ i j = φ (eOf M τ i j) := by
  intro E _ _ a d D φ M h
  refine ⟨fun i j => ?_, ?_⟩
  · have e : (fun y => φ (M y) i j) = ∑ k, ∑ l, (φ (Matrix.single k l 1) i j) • fun y => M y k l := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact lin_entry φ (M y) i j
    rw [e]
    exact Subalgebra.sum_mem _ fun l _ => Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _ (h l k) _
  · have hd : ∀ X, dOf (fun y => φ (M y)) X = φ (dOf M X) := by
      intro X
      ext i j
      have h1 := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ =>
        HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => (h.diff k l).const_mul (φ (Matrix.single k l 1) i j)
      have h2 := h1.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => φ (M y) i j)
        (fun y => by simp only [extGL_val]; exact lin_entry φ (M y) i j) (x := oneL E a) isUnit_one)
      rw [lin_entry φ (dOf M X), dOf, Matrix.of_apply, h2.fderiv]
      simp [dOf]
    intro τ i j
    simp only [eOf, hd, map_smul, map_sub]
