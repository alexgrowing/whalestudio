import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
import Formalism.SharpRestriction.CuspSpanNormBounds.SchurRelationsDiscreteSeries
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AIsL

namespace CompanionTheory.Lime.BM

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

theorem multiplicity_one_unitary_branching_of_uniqGap (hJ : UniqGap) (D : D7) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : LocalBesselAndTopKernel.MultiplicityOneUnitaryBranching D := by
  intro τ u H _ _ σ Wp _ _ π z B1 B2 hσ hπ hz hT hB1 hB2 _ _ _ _
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hl : IsHCParam (lamSH D.R (D.hc τ)) := Inh.obj_isHCParam_lamSH D.R (D.hc τ)
  have hga := gap_at_least_of_low_gap D.R.k D.R.rS (v48 D τ) (b48 D τ) _ hk (by rw [lambda_highest_weight_eq]; exact hl.1)
    (Formalism.L2.SG.Pf.WuDec.lowGap_of_gapHyp D hG τ)
  rw [lambda_highest_weight_eq, epsilon_signature_eq] at hga
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (16 * (D.R.r : ℝ) ^ 19) := by
    have := Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS hk (by rw [Formalism.L2.SG.Pf.WuDec.dimS D]; exact hG.1)
    rwa [Formalism.L2.SG.Pf.WuDec.dimS D] at this
  by_cases h1 : ∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) σ, B1 v = 0
  · exact Or.inl h1
  · push Not at h1
    unfold psiS at hB1 hB2
    rw [Formalism.L2.SG.LitS.psi_eq_psiGen] at hB1 hB2
    exact Or.inr (aIsL hJ hga hok hl hσ (SchurRelationsDiscreteSeries.inWb_of_zero z hz) hT (fun _ => SchurRelationsDiscreteSeries.psiS_scale_ne D) hπ
      ((BridgeCS3d.isBesselMapSm_iff z _ σ π B2).1 hB2) ((BridgeCS3d.isBesselMapSm_iff z _ σ π B1).1 hB1) h1)

end CompanionTheory.Lime.BM
