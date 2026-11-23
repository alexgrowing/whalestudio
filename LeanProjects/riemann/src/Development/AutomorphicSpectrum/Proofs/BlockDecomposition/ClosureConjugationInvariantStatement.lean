import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureConjugationInvariant
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_conjugation_invariant : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, ∀ a ∈ SuppAt d β {w}, ∀ c : (Q d β (AF F))ˣ,
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) →
    a ∈ closure (SAQ d β s) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem | exact GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem <;> assumption)
