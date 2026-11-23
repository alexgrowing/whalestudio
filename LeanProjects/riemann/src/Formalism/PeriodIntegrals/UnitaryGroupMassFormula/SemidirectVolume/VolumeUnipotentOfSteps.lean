import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory

theorem volume_unipotent_of_steps (hSub : SubLCSC) (hFD : FDExG) (hPr : ProdHaarG) (hV : VolG)
    (hLC : LcscHA) (hD : DiscHA) (hCl : ClosedStep) (hSe : SemiStep) (hCo : ConjStep) :
    PI.VolSemiDirect.VolumeUnipotentAllCM := by
  intro F E _ _ _ _ _ σ hCM M J hJ hJ' r P T hr hP μN hμN μH hμH
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  have hX := hLC F E σ hCM M J hJ
  obtain ⟨hcnt, hdisc⟩ := hD F E σ hCM M J hJ
  obtain ⟨cS, cN, cH⟩ := hCl F E σ hCM M J hJ r P T hr hP
  obtain ⟨hsemi, hrat⟩ := hSe F E σ hCM M J hJ r P T hr hP
  have hconj := hCo F E σ hCM M J hJ r P T hr hP
  obtain ⟨lS, dS⟩ := hSub (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cS hcnt hdisc
  obtain ⟨lN, dN⟩ := hSub (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cN hcnt hdisc
  obtain ⟨lH, dH⟩ := hSub (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cH hcnt hdisc
  obtain ⟨μ0, hμ0, hp0⟩ := hPr (HA (AF F) σ J) _ _ _ hsemi lS lN lH hconj μN hμN μH hμH
  obtain ⟨𝓕0, -, h𝓕0⟩ := hFD (HA (AF F) σ J) (HFinIn (AF F) σ J) _ lS dS
  obtain ⟨𝓕N0, -, h𝓕N0⟩ := hFD (HA (AF F) σ J) (HFinIn (AF F) σ J) _ lN dN
  obtain ⟨𝓕H0, -, h𝓕H0⟩ := hFD (HA (AF F) σ J) (HFinIn (AF F) σ J) _ lH dH
  unfold AllSome
  refine ⟨⟨μ0, hμ0, hp0⟩, ?_⟩
  rintro μS ⟨hμS, hpS⟩
  refine ⟨⟨𝓕0, h𝓕0 μS⟩, fun 𝓕 h𝓕 => ⟨⟨𝓕N0, h𝓕N0 μN⟩, fun 𝓕N h𝓕N =>
    ⟨⟨𝓕H0, h𝓕H0 μH⟩, fun 𝓕H h𝓕H => ?_⟩⟩⟩
  exact hV (HA (AF F) σ J) _ _ _ _ hsemi hrat lS lN lH dS dN dH μS μN μH hμS hμN hμH hpS 𝓕 𝓕N 𝓕H h𝓕 h𝓕N h𝓕H

end PI.VolSemiDirect.W
