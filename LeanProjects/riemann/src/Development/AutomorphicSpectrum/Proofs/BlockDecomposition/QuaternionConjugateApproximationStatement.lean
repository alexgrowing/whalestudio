import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionConjugateApproximation
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionNeighbourhoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRamifiedPlacesFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionIntegralTraceAlmostAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDenseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionTraceOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSquareRootsNearOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionAnisotropicTraceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleNormTraceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionLocalUnitsStatement
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_conjugate_approximation : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 → ∀ V ∈ 𝓝 a,
    ∃ b ∈ V, ∃ y : (Q d β (AF F))ˣ, ∃ x : Q d β F, qn x = 1 ∧ ∃ h ∈ SuppAt d β {s},
      (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = b * h := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.KeyApprox.keyapprox | exact GlobalTheory.CompanionTheory.PlaneSA.KeyApprox.keyapprox | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.KeyApprox.keyapprox <;> assumption)
