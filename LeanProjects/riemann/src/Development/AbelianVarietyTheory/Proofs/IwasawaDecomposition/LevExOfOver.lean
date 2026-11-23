import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

private theorem levEx_of_levelPrimes_eq (D : D7) (S : Finset ℕ) (g : Fin 2 → ℕ) (a b c : ℕ) (hS : S = {g 0, g 1, a, b, c})
    (hlev : ∀ p, p ∈ D.host.levelPrimes ↔ p ∈ S ∨ ∃ u, p = (D.mem u).A.T)
    (hg : ∀ i, D.host.g i = g i) (ha : D.host.pde = a) (hb : D.host.pde' = b) (hc : q0Av D = c) : LevEx D := by
  intro p
  rw [hlev, hS]
  simp only [Finset.mem_insert, Finset.mem_singleton, hg, ha, hb, hc, Fin.exists_fin_two]
  tauto

theorem levEx_of_over : ∀ (D : D7) (P : PreCh) (Lv : LevCh P), Over D P Lv →
    P.H.levelPrimes = {P.H.g 0, P.H.g 1, P.H.pde, P.H.pde', DC.q0H P.H} → LevEx D ∧ ∀ N h, LevEx (setDiv D N h) := by
  intro D P Lv hO hlev
  obtain ⟨sp, hT, hY, hA, hV, hz, X, hX, rfl⟩ := hO
  refine (fun hD => ⟨hD, fun _ _ => hD⟩) ?_
  obtain ⟨B, C, W, V, S, Ns, G⟩ := X
  cases B
  dsimp only at hX
  subst hX
  refine levEx_of_levelPrimes_eq _ P.H.levelPrimes P.H.g P.H.pde P.H.pde' (DC.q0H P.H) hlev ?_ (fun _ => rfl) rfl rfl ?_
  · intro p
    have hT' := C.A_T
    show p ∈ P.H.levelPrimes ∪ Finset.univ.image Lv.T ↔ _
    rw [Finset.mem_union, Finset.mem_image]
    exact or_congr Iff.rfl
      ⟨fun ⟨u, _, hu⟩ => ⟨u, hu.symm.trans (hT' u).symm⟩, fun ⟨u, hu⟩ => ⟨u, Finset.mem_univ _, (hT' u).symm.trans hu.symm⟩⟩
  · unfold q0Av DC.q0H rPrAv DC.rPrH LevelStarExponents.condE
    rfl

end GlobalTheory.Mem.HD
