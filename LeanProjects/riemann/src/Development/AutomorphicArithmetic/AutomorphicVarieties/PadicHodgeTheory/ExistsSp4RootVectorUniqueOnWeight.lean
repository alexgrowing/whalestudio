import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private def rootEnt (a b i j : Fin 4) : ℤ :=
  if i = a ∧ j = b then 1 else if j.rev = a ∧ i.rev = b then -(sgn i * sgn j) else 0

private theorem rootEnt_adj : ∀ a b i j : Fin 4, a ≠ b →
    (sgn i * sgn j) * rootEnt a b j.rev i.rev = -rootEnt a b i j := by decide

private theorem rootEnt_zero : ∀ a b i j : Fin 4, wt i j ≠ wt a b → rootEnt a b i j = 0 := by decide

private theorem rootEnt_cases : ∀ a b i j : Fin 4, a ≠ b → wt i j = wt a b →
    (i = a ∧ j = b) ∨ (j.rev = a ∧ i.rev = b ∧ rootEnt a b i j = -(sgn i * sgn j)) := by decide

theorem UpperTheory.exists_sp4_root_vector_unique_on_weight :
    ∀ (E : Type) [Field E] [CharZero E] (a b : Fin 4), a ≠ b → ∃ X ∈ sp4 E, X a b = 1 ∧ (∀ i j, wt i j ≠ wt a b → X i j = 0) ∧ ∀ Y ∈ sp4 E, ∀ i j, wt i j = wt a b → Y i j = Y a b * X i j := by
  intro E _ _ a b hab
  refine ⟨Matrix.of fun i j => ((rootEnt a b i j : ℤ) : E), ?_, ?_, ?_, ?_⟩
  · show UpperTheory.V.GradeZeroInterpolatingElement.adj _ = -_
    ext i j
    rw [adj_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, zsmul_eq_mul, ← Int.cast_mul,
      rootEnt_adj a b i j hab, Int.cast_neg]
  · simp [rootEnt]
  · intro i j h
    simp [rootEnt_zero a b i j h]
  · intro Y hY i j h
    rcases rootEnt_cases a b i j hab h with ⟨rfl, rfl⟩ | ⟨h1, h2, h3⟩
    · simp [rootEnt]
    · have hY' : UpperTheory.V.GradeZeroInterpolatingElement.adj Y = -Y := hY
      have h4 := congrFun (congrFun hY' i) j
      rw [adj_apply, Matrix.neg_apply, h1, h2, zsmul_eq_mul] at h4
      rw [Matrix.of_apply, h3, Int.cast_neg]
      linear_combination h4
