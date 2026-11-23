import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormElementCongruence
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_element_congruence : PrN → AllSt fun _ _ _ _ _ _ x => ∀ i, ((Dof x).host.g i).Prime ∧ ∃ π : 𝓞 (Dof x).host.E, (π : (Dof x).host.E) ∈ (Dof x).host.K ∧ (π : (Dof x).host.E) * (Dof x).host.conj (π : (Dof x).host.E) = ((Dof x).host.g i : (Dof x).host.E) ∧ (π - 1) ∈ Ideal.span {(((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d : ℕ) : 𝓞 (Dof x).host.E)} := by
  first | exact @GlobalTheory.HeightCounting.Up.gnorm_allSt | exact GlobalTheory.HeightCounting.Up.gnorm_allSt | (intros; apply GlobalTheory.HeightCounting.Up.gnorm_allSt <;> assumption)
