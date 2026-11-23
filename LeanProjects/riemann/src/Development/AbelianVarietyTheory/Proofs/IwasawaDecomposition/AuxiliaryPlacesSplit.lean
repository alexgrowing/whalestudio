import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem isSplitPl_of_mem_levelPrimes {R : Ranks} (H : Host R)
    (hc : ∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) {p : ℕ} (hp : p ∈ H.levelPrimes)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E p) : IsSplitPl H v := by
  obtain ⟨hpr, hm⟩ := hc p hp
  have h := (GlobalTheory.HostSplit.split_of_one_mod R H p hpr hm).1
  obtain ⟨-, he, hf⟩ := GlobalTheory.unramified_degree_one_of_ncard_placesOver H.E p hpr h v hv
  exact GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSplitPl_of_degree_one H v hf he

theorem split_allSt : PrN → AllSt fun _ _ _ _ _ _ x => ∀ v : HeightOneSpectrum (𝓞 (Dof x).host.E), v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x v hv => ?_
  have hc : ∀ p ∈ (Dof x).host.levelPrimes, p.Prime ∧ p % ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) = 1 :=
    (w.st x.o.Z).B.level_cond
  rcases hv with hv | hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.1 v hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.2 v hv

end GlobalTheory.HeightCounting.Up
