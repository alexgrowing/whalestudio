import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantGLOfEquivariantUnitaryCoefficientSpac
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
open Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_GL_of_equivariant_unitary_coefficientSpace : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n) (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ), (∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))) v) = rhoK σ (fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)) (φ v)) → ∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v) := by
  first | exact @GlobalTheory.Branching.Family.equivariant_gl_of_unitary | exact GlobalTheory.Branching.Family.equivariant_gl_of_unitary | (intros; apply GlobalTheory.Branching.Family.equivariant_gl_of_unitary <;> assumption)
