import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PxIsCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinLamOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FirstPrimeConditionTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ComponentsGoodRankTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL3

theorem UpperTheory.V.J.absGood :
    UpperTheory.V.J.AbsGood := by
  intro l _ O _ _ _ _ _ F T₂ T₃ J₂ J₃ h₂ h₃
  obtain ⟨φ₂, hφ₂, hs₂⟩ := UpperTheory.V.Pr.phiEx l O F 2 T₂
  obtain ⟨φ₃, hφ₃, hs₃⟩ := UpperTheory.V.Pr.phiEx l O F 3 T₃
  obtain ⟨Λ₂, hΛ₂⟩ := h₂.fin
  obtain ⟨Λ₃, hΛ₃⟩ := h₃.fin
  have good₂ : UpperTheory.V.Pr.AllGood T₂.S (Ideal.map φ₂ J₂) :=
    UpperTheory.V.Pr.components_good_rank_two l O F T₂.C₀ T₂.ok T₂.big T₂.S (Ideal.map φ₂ J₂)
      (UpperTheory.V.Pr.finLamOf l O F 2 T₂ φ₂ hφ₂ hs₂ Λ₂ J₂ hΛ₂)
      (UpperTheory.V.Pr.p1Of l O F 2 T₂ φ₂ hφ₂ h₂.n4 J₂ h₂.p1)
      (UpperTheory.V.Pr.seedOf l O F 2 T₂ φ₂ hφ₂ J₂ h₂.unr h₂.dim h₂.seed)
  refine ⟨φ₃, hφ₃, hs₃, ?_⟩
  exact (UpperTheory.V.Pr.components_good_rank_three l O F T₃.C₀ T₃.ok T₃.big T₂.S (Ideal.map φ₂ J₂)
      (UpperTheory.V.Pr.finLamOf l O F 2 T₂ φ₂ hφ₂ hs₂ Λ₂ J₂ hΛ₂) good₂
      T₃.S (Ideal.map φ₃ J₃)
      (UpperTheory.V.Pr.finLamOf l O F 3 T₃ φ₃ hφ₃ hs₃ Λ₃ J₃ hΛ₃)
      (UpperTheory.V.Pr.p1Of l O F 3 T₃ φ₃ hφ₃ h₃.n4 J₃ h₃.p1)
      (UpperTheory.V.Pr.rankThree_deformationSetup_splitting_condition l O F T₃ φ₃ hφ₃ h₃.n4 J₃ h₃.p3)
      (UpperTheory.V.Pr.seedOf l O F 3 T₃ φ₃ hφ₃ J₃ h₃.unr h₃.dim h₃.seed)).1
