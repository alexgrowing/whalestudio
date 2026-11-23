import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSelfDualMeasuresFibreFamilyExistStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarFrameStabilizerLocalFixerSectionProductStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibreStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimilitudeConjPreservesUnitaryHaarAtFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiVNeOneOfTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualTrace
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalStabiliserTie

theorem exists_tied_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → 2 * (r + 1) < n → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW σ J ψ v P μG μS := by
  intro F E _ _ _ _ _ σ hcm n J hJ hW hC ψ hψ hstd v r P T hP hn μG hG
  obtain ⟨-, -, hT, -, -⟩ := GlobalTheory.FrameGram.std_frame_gram F E σ hcm n J hJ r P T hP
  obtain ⟨hdX, hdT, hOm⟩ := GlobalTheory.T.localSelfDualMeasures_fibreFamily_exist F E σ hcm n J hJ hW hC ψ hψ v (r + 1) (by omega) hn
  have hfib : IsFibreFamily (Formalism.L2.SG.LocVol.dX σ J ψ v (r + 1)) (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} (Formalism.L2.SG.LocVol.dT σ ψ v (r + 1)) Set.univ
      (Formalism.L2.SG.LocVol.omFam σ J ψ v (r + 1)) := hOm
  obtain ⟨μ0, hμ0, hc1, hc2⟩ := GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre F E σ hcm n J hJ v r P T hP hT _ _ hdX hdT _ hfib μG hG
  have hconj := GlobalTheory.T.similitude_conj_preserves_unitary_haar_at_finite_place F E σ hcm n J hJ v r P T hP hT _ _ hdX hdT _ hfib μ0 hμ0
  have hne : ∃ x, psiV F ψ v x ≠ 1 := GlobalTheory.StdCharTotReal.exists_psiV_ne_one F hcm.1 ψ hψ hstd v
  have hsd := GlobalTheory.TraceSelfDual.exists_selfDual_trace F E σ hcm ψ hψ v hne (Formalism.L2.SG.LocVol.UIdx r)
  have hU : (Formalism.L2.SG.LocVol.sdE (E := E) ψ v (Formalism.L2.SG.LocVol.UIdx r)).IsAddHaarMeasure := by
    unfold Formalism.L2.SG.LocVol.sdE
    rw [dif_pos hsd]
    exact hsd.choose_spec.1
  obtain ⟨μS, hμS, hprod⟩ := GlobalTheory.T.haar_frameStabilizer_local_fixer_section_product F E σ hcm n J hJ v r P T hP μ0 hμ0 hconj _ hU
  refine ⟨μS, hμS, μ0, hμ0, ?_, ?_⟩
  · have hom : Formalism.L2.SG.LocVol.omAt σ J ψ v (Formalism.L2.SG.LocVol.TFl σ J v P)
        = Formalism.L2.SG.LocVol.omFam σ J ψ v (r + 1) (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT) := by
      unfold Formalism.L2.SG.LocVol.omAt
      have hmem : Formalism.L2.SG.LocVol.TFl σ J v P ∈ HermR (Fv F v) σ (r + 1) :=
        map_mem_HermR (Fv F v) σ _ hT
      rw [dif_pos hmem]
      rfl
    unfold Formalism.L2.SG.LocVol.IsCompatLoc
    rw [hom]
    exact ⟨hc1, hc2⟩
  · intro h hh t ht
    exact hprod h hh t ht

end GlobalTheory.LocalStabiliserTie
