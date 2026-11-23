import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentIntegralValuedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem eigenExponent_isIntegral_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ (j : Fin (Dof x).R.m) (g : ↥((Dof x).R.Psi)), ∃ z : ℤ, eExp (Dof x) j g = (z : ℚ) := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x j g => ?_
  exact ((Dof x).hc ((Dof x).eTau.symm g)).e_int j
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eExp_integral_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ (j : Fin (Dof x).R.m) (g : ↥((Dof x).R.Psi)), ∃ z : ℤ, eExp (Dof x) j g = (z : ℚ) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.eigenExponent_isIntegral_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.eigenExponent_isIntegral_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.eigenExponent_isIntegral_all_stages_alt <;> assumption)
end
end
