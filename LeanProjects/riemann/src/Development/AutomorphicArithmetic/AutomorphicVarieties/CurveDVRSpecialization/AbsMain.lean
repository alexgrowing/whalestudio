import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PxIsCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinLamOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FirstPrimeConditionTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GoodPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ComponentsGoodRankTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL3
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinPtOf

theorem UpperTheory.V.Pr.absMain :
    UpperTheory.V.Pr.AbsMain := by
  intro l _ O _ _ _ _ _ F T₂ T₃ J₂ J₃ m₂ m₃
  obtain ⟨Φ₂, hΦ₂, hs₂⟩ := UpperTheory.V.Pr.phiEx l O F 2 T₂
  obtain ⟨Φ₃, hΦ₃, hs₃⟩ := UpperTheory.V.Pr.phiEx l O F 3 T₃
  obtain ⟨Λ₂, hΛ₂⟩ := m₂.fin
  obtain ⟨Λ₃, hΛ₃⟩ := m₃.fin
  have fl₂ := UpperTheory.V.Pr.finLamOf l O F 2 T₂ Φ₂ hΦ₂ hs₂ Λ₂ J₂ hΛ₂
  have fl₃ := UpperTheory.V.Pr.finLamOf l O F 3 T₃ Φ₃ hΦ₃ hs₃ Λ₃ J₃ hΛ₃
  have p₂ := UpperTheory.V.Pr.p1Of l O F 2 T₂ Φ₂ hΦ₂ m₂.n4 J₂ m₂.p1
  have p₃ := UpperTheory.V.Pr.p1Of l O F 3 T₃ Φ₃ hΦ₃ m₃.n4 J₃ m₃.p1
  have q₃ := UpperTheory.V.Pr.rankThree_deformationSetup_splitting_condition l O F T₃ Φ₃ hΦ₃ m₃.n4 J₃ m₃.p3
  have s₂ := UpperTheory.V.Pr.seedOf l O F 2 T₂ Φ₂ hΦ₂ J₂ m₂.unr m₂.dim m₂.seed
  have s₃ := UpperTheory.V.Pr.seedOf l O F 3 T₃ Φ₃ hΦ₃ J₃ m₃.unr m₃.dim m₃.seed
  have g₂ := UpperTheory.V.Pr.components_good_rank_two l O F T₂.C₀ T₂.ok T₂.big T₂.S _ fl₂ p₂ s₂
  obtain ⟨g₃, off⟩ := UpperTheory.V.Pr.components_good_rank_three l O F T₃.C₀ T₃.ok T₃.big T₂.S _ fl₂ g₂ T₃.S _ fl₃ p₃ q₃ s₃
  exact ⟨UpperTheory.V.Pr.goodPtOf l O F 2 T₂ Φ₂ hΦ₂ J₂ g₂,
    UpperTheory.V.Pr.goodPtOf l O F 3 T₃ Φ₃ hΦ₃ J₃ g₃,
    UpperTheory.V.Pr.finPtOf l O F T₃.C₀ T₃.ok T₃.S off⟩
