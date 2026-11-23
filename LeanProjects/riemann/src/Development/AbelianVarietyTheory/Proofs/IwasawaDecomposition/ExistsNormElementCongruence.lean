import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem gnorm_allSt : PrN → AllSt fun _ _ _ _ _ _ x => ∀ i, ((Dof x).host.g i).Prime ∧ ∃ π : 𝓞 (Dof x).host.E, (π : (Dof x).host.E) ∈ (Dof x).host.K ∧ (π : (Dof x).host.E) * (Dof x).host.conj (π : (Dof x).host.E) = ((Dof x).host.g i : (Dof x).host.E) ∧ (π - 1) ∈ Ideal.span {(((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d : ℕ) : 𝓞 (Dof x).host.E)} := by
  intro _
  have aux : ∀ (K : Ctx) (Q : Pre), K.Over Q → ∀ i, (Q.host.g i).Prime ∧ ∃ π : 𝓞 Q.host.E, (π : Q.host.E) ∈ Q.host.K ∧
      (π : Q.host.E) * Q.host.conj (π : Q.host.E) = (Q.host.g i : Q.host.E) ∧
      (π - 1) ∈ Ideal.span {((Q.host.QS * Q.host.q * Q.host.d : ℕ) : 𝓞 Q.host.E)} := by
    rintro K Q ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ i
    exact ⟨K.P.H.g_prime i, K.ok.gnorm i⟩
  refine StepW.of_all fun K B f T w hO _ _ => ?_
  intro P x i
  exact aux K B.toPre hO i

end GlobalTheory.HeightCounting.Up
