import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlanePropOfAllStrongApproxStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmExtensionImaginaryGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneApproxOfQuaternionApproxStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionIsotropicSplitAllPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportProductOverPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrongApproxClosureMulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportClosureRegularTraceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjClosureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureConjugationInvariantStatement

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem aniso {F : Type} [Field F] [NumberField F] (d β : F) (hanis : ∀ x : Q d β F, qn x = 0 → x = 0)
    (s : Pl F) (hs : ∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) : QSA d β s := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    have := hanis ⟨0, 1, 0, 0⟩ (by simp [qn])
    simpa using congrArg QuaternionAlgebra.imI this
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have := hanis ⟨0, 0, 1, 0⟩ (by simp [qn])
    simpa using congrArg QuaternionAlgebra.imJ this
  have one_mem : (1 : Q d β (AF F)) ∈ SAQ d β s :=
    ⟨1, qn_one, 1, ⟨qn_one, fun u _ => map_one _⟩, by simp⟩
  intro T g hg
  refine GlobalTheory.T.support_product_over_places d β _ (subset_closure one_mem) (GlobalTheory.T.strong_approx_closure_mul d β s) (fun w a ha => ?_) T hg
  by_cases hw : w = s
  · subst hw
    exact subset_closure ⟨1, qn_one, a, ha, by simp⟩
  · have hreg := GlobalTheory.T.support_closure_regular_trace d β hd0 hβ0 w a ha
    refine closure_minimal (fun a' ha' => ?_) isClosed_closure hreg
    obtain ⟨c, hc⟩ := GlobalTheory.T.quaternion_norm_one_conj_closure d β hanis s w hs hw a' ha'.1 ha'.2
    exact GlobalTheory.T.closure_conjugation_invariant d β hanis s w a' ha'.1 c hc

theorem plane : Sa2.PropPlane := by
  refine GlobalTheory.T.plane_prop_of_all_strong_approx ?_
  intro F E _ _ _ _ _ σ hcm β hβ
  obtain ⟨d, hd, ξ, hξ, hσ⟩ := GlobalTheory.T.cm_extension_imaginary_generator σ hcm
  refine GlobalTheory.T.plane_approx_of_quaternion_approx σ hcm β hβ d hd ξ hξ hσ fun s hs => ?_
  by_cases hanis : ∀ x : Q d β F, qn x = 0 → x = 0
  · exact aniso d β hanis s hs
  · push Not at hanis
    obtain ⟨x, hx, hx0⟩ := hanis
    exact GlobalTheory.T.quaternion_isotropic_split_all_places d β hd hβ ⟨x, hx0, hx⟩ s

end GlobalTheory.CompanionTheory.PlaneSA
