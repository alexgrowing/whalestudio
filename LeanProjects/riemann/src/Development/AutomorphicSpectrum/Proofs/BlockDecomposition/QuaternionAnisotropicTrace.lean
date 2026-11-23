import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem anis_trace_sq_sub_four_ne_sq :
    ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 →
      (∀ x : Q d β K, qn x = 0 → x = 0) → ∀ b : Q d β K, qn b = 1 → b.re ^ 2 ≠ 1 →
      ∀ r : K, r ^ 2 ≠ (2 * b.re) ^ 2 - 4 := by
  intro F K _ _ _ d β h2 han b hb hre r hr
  have hz : qn (⟨r, 2 * b.imI, 2 * b.imJ, 2 * b.imK⟩ : Q d β K) = 0 := by
    simp only [qn] at hb ⊢
    linear_combination hr + 4 * hb
  have h0 := han _ hz
  have hI : b.imI = 0 := by
    have := congrArg QuaternionAlgebra.imI h0
    simpa [h2] using this
  have hJ : b.imJ = 0 := by
    have := congrArg QuaternionAlgebra.imJ h0
    simpa [h2] using this
  have hK : b.imK = 0 := by
    have := congrArg QuaternionAlgebra.imK h0
    simpa [h2] using this
  apply hre
  simpa [qn, hI, hJ, hK] using hb

end GlobalTheory.CompanionTheory.PlaneSA
