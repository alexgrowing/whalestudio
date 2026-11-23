import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjClosure
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionConjugateApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionClassNumberFiniteStatement
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_norm_one_conj_closure : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 →
    ∃ c : (Q d β (AF F))ˣ, ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.ConjStep.exists_conj_mem_closure | exact GlobalTheory.CompanionTheory.PlaneSA.ConjStep.exists_conj_mem_closure | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.ConjStep.exists_conj_mem_closure <;> assumption)
