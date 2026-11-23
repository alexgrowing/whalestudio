import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension

open Formalism.ConjugateSelfDual IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.automorphic_forms_descent_to_smaller_level :
    UpperTheory.V.Sd.S2.Descend := by
  intro l _ c
  refine ⟨UpperTheory.V.Fr.sc_norm l c, ?_⟩
  intro ι Γ _ _ _ _ _ _ P hc hr hn
  obtain ⟨E, hE, hEr⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 4 P.r.toHomUnits
    fun i j => hc.matrix_elem i j
  let s : Set (PadicAlgCl l) := Set.range fun p : ι × Fin 4 × Fin 4 => P.n p.1 p.2.1 p.2.2
  haveI : Finite s := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  obtain ⟨c₁, hcc, h₁⟩ := (UpperTheory.integrality_of_norm_coefficients l).1 c (IntermediateField.adjoin ℚ_[l] s ⊔ E) inferInstance
  have hr₁ : ∀ g i j, P.r g i j ∈ c₁.O := fun g i j =>
    h₁ _ ((le_sup_right : E ≤ _) (hEr g i j)) (hr g i j)
  have hn₁ : ∀ v i j, P.n v i j ∈ c₁.O := fun v i j =>
    h₁ _ ((le_sup_left : IntermediateField.adjoin ℚ_[l] s ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(v, i, j), rfl⟩)) (hn v i j)
  let ρ : Γ →* M4 c₁.O :=
    { toFun := fun g => Matrix.of fun i j => ⟨P.r g i j, hr₁ g i j⟩
      map_one' := by
        ext i j
        simp only [map_one, Matrix.of_apply, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp only [map_mul, Matrix.of_apply, Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul] }
  refine ⟨c₁, hcc, ⟨ρ, fun v => Matrix.of fun i j => ⟨P.n v i j, hn₁ v i j⟩⟩, ?_, fun i j => ?_⟩
  · exact PD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => rfl) (funext fun v => Matrix.ext fun i j => rfl)
  · exact ((UpperTheory.integrality_of_norm_coefficients l).2 c₁ Γ _).2 (hc.matrix_elem i j)
