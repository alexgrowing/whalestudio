import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FlathTensorProduct
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnitaryIrreducibleAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_irreducible_smooth_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NonarchimedeanGroup G] [LocallyCompactSpace G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : G →* (H →L[ℂ] H)), IsIrrUnitary π → (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional ℂ (fixed (toRep π) K)) → (smRep π).IsIrreducible ∧ IsAdmissible (smRep π) := by
  first | exact @GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep | exact GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep | (intros; apply GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep <;> assumption)
