import Mathlib
import Formalism.PeriodIntegrals.VolNzeroOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NilpotentVolumeOne.LinearIndependentFrameWithNormal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SubgroupLocallyCompactHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.FundamentalDomainExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.DiscAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary

noncomputable section

namespace PI.VolNzeroOne.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Measure
open scoped TensorProduct ENNReal NNReal

theorem volume_degenerate_rank_one : PI.VolNzeroOne.VolumeUnipotentOneFrom := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSW hStab hS0 hN0 hJ' r P T hr hP hT0 hT1
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  have hX := PI.VolSemiDirect.W.Lc.locally_compact_adelic_unitary F E σ hCM M J hJ
  obtain ⟨hcnt, hdisc⟩ := PI.VolSemiDirect.W.discrete_adelic_unitary F E σ hCM M J hJ
  obtain ⟨cS, cN, -⟩ := PI.VolSemiDirect.W.closed_subgroup_holds F E σ hCM M J hJ r P T hr hP
  obtain ⟨lS, -⟩ := PI.VolSemiDirect.W.subgroup_locally_compact_holds (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cS
    hcnt hdisc
  obtain ⟨lN, dN⟩ := PI.VolSemiDirect.W.subgroup_locally_compact_holds (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cN
    hcnt hdisc
  have lN' := lN
  obtain ⟨lcS, scS, t2S, tgS⟩ := lS
  obtain ⟨lcN, scN, t2N, tgN⟩ := lN
  obtain ⟨lcG, scG, t2G, tgG⟩ := hX

  have hA : VolStabAt F E σ M J (F0 P) hT0 :=
    hS0 hJ' r (by omega) (F0 P) (-T) (neg_ne_zero.2 hP.2.2.2.2.2.2) (linearIndependent_frame_with_normal σ J P T hP hT1)
      (gram_frame_with_normal_eq_diag σ J P T hP hT0) hT0
  have hB : VolStabAt F E σ M J (tupH P) hT1 :=
    hStab hJ' (r + 1 + r) (by omega) (by omega) (tupH P) hT1 (det_gram_tupH_ne_zero σ J P T hP hT1)
  unfold VolStabAt AllSome at hA hB
  unfold SWa1 AllSome at hSW
  unfold AllSome
  obtain ⟨⟨ψ0, hψ0⟩, hA1⟩ := hA
  obtain ⟨-, hB1⟩ := hB
  refine ⟨⟨ψ0, hψ0⟩, fun ψ hψ => ?_⟩
  obtain ⟨⟨μ0, hμ0⟩, hA2⟩ := hA1 ψ hψ
  obtain ⟨-, hB2⟩ := hB1 ψ hψ
  refine ⟨⟨μ0, hμ0⟩, fun μ hμ => ?_⟩
  obtain ⟨⟨νS0, hνS0⟩, hA3⟩ := hA2 μ hμ
  obtain ⟨⟨νH0, hνH0⟩, hB3⟩ := hB2 μ hμ
  refine ⟨⟨νS0, hνS0⟩, fun νS hνS => ?_⟩
  obtain ⟨⟨μS0, hμS0⟩, hA4⟩ := hA3 νS hνS
  refine ⟨⟨μS0, hμS0⟩, fun μS hμS => ?_⟩
  refine ⟨⟨νH0, hνH0⟩, fun νH hνH => ?_⟩
  obtain ⟨⟨μH0, hμH0⟩, hB4⟩ := hB3 νH hνH
  refine ⟨⟨μH0, hμH0⟩, fun μH hμH => ?_⟩

  obtain ⟨⟨𝓕0, h𝓕0⟩, hA5⟩ := hA4 μS hμS
  obtain ⟨⟨𝓕S, h𝓕S⟩, hA6⟩ := hA5 𝓕0 h𝓕0
  have eS : μS 𝓕S = μ 𝓕0 := hA6 𝓕S h𝓕S
  obtain ⟨-, hB5⟩ := hB4 μH hμH
  obtain ⟨⟨𝓕H, h𝓕H⟩, hB6⟩ := hB5 𝓕0 h𝓕0
  have eH : μH 𝓕H = μ 𝓕0 := hB6 𝓕H h𝓕H

  have hfin : μ 𝓕0 < ⊤ := (hSW.2 μ hμ).2 𝓕0 h𝓕0
  have hpos : μ 𝓕0 ≠ 0 := by
    have : μ.IsHaarMeasure := hμ
    have : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
      ⟨fun c ⦃s⦄ _ => measure_preimage_mul μ (c.1 : HA (AF F) σ J) s⟩
    have hne : μ ≠ 0 := by
      intro h
      have h1 : 0 < μ Set.univ := isOpen_univ.measure_pos (μ := μ) Set.univ_nonempty
      rw [h] at h1
      simp at h1
    exact IsFundamentalDomain.measure_ne_zero hne h𝓕0
  have : μS.IsHaarMeasure := hμS.1
  have : μH.IsHaarMeasure := hμH.1
  refine ⟨?_, fun μN hμN => ?_⟩
  ·
    obtain ⟨⟨μS1, hμS1, hp1⟩, -⟩ := hN0 hJ' r P T hr hP (haar : Measure (FrameUnipotentSubgroup (AF F) σ J P))
      inferInstance μH hμH.1
    have := hμS1
    obtain ⟨c, hc, heq⟩ : ∃ c : ℝ≥0, 0 < c ∧ μS = c • μS1 :=
      ⟨_, haarScalarFactor_pos_of_isHaarMeasure μS μS1, isMulLeftInvariant_eq_smul μS μS1⟩
    refine ⟨c • (haar : Measure (FrameUnipotentSubgroup (AF F) σ J P)), IsHaarMeasure.nnreal_smul (μ := (haar : Measure (FrameUnipotentSubgroup (AF F) σ J P))) hc.ne', ?_⟩
    intro f hf
    rw [heq, lintegral_smul_measure, hp1 f hf, lintegral_smul_measure]
  · obtain ⟨𝓕N0, -, h𝓕N0⟩ :=
      PI.VolSemiDirect.W.fundamental_domain_exists (HA (AF F) σ J) (HFinIn (AF F) σ J) _ lN' dN
    refine ⟨⟨𝓕N0, h𝓕N0 μN⟩, fun 𝓕N h𝓕N => ?_⟩
    obtain ⟨-, k1⟩ := hN0 hJ' r P T hr hP μN hμN.1 μH hμH.1
    obtain ⟨-, k2⟩ := k1 μS ⟨hμS.1, hμN.2⟩
    obtain ⟨-, k3⟩ := k2 𝓕S h𝓕S
    obtain ⟨-, k4⟩ := k3 𝓕N h𝓕N
    have e := k4 𝓕H h𝓕H
    rw [eS, eH] at e
    exact (ENNReal.mul_left_inj hpos hfin.ne).1 (by rw [one_mul]; exact e.symm)

end PI.VolNzeroOne.W
