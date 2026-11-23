import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSpecializationTwistSatisfiesFirstCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSpecializationTwistSatisfiesThirdCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceTypeE

theorem UpperTheory.V.Pr.niceOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.NiceOf := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hp h1 h2
  refine ⟨UpperTheory.V.Pr.nice_specialization_twist_satisfies_first_condition l O F n T x L y j hj hp h1 h2, UpperTheory.V.Pr.nice_specialization_twist_satisfies_third_condition l O F n T x L y j hj hp h1 h2,
    fun hI => ?_, fun hE => ?_⟩
  · have h := UpperTheory.V.Pr.niceIrr l O F n T x L y j hj hp h1 h2 hI ⊤ (by simp)
    rw [top_inf_eq] at h
    exact h
  · obtain rfl : n = 3 := hE.2.1
    exact UpperTheory.V.Pr.niceTypeE l O F T x L y j hj hp h1 h2 hE
