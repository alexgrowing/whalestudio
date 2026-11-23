import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceGramDetNeZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuples
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteComponentCoordinatesAction

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth

section Gen
open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

def chiG (G : Matrix ι ι F) (u v : ι → 𝔸[F]) : ℂ :=
  (adelicChar F (u ⬝ᵥ (G.map (algebraMap F 𝔸[F]) *ᵥ v)) : ℂ)

def mulHomeo (A B : Matrix ι ι 𝔸[F]) (hAB : A * B = 1) (hBA : B * A = 1) : (ι → 𝔸[F]) ≃ₜ (ι → 𝔸[F]) where
  toFun u := A *ᵥ u
  invFun u := B *ᵥ u
  left_inv u := by simp only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  right_inv u := by simp only [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

end Gen

section Link
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.CompanionTheory.SW.BB
open scoped TensorProduct ENNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def tupOf {M d : ℕ} (b : Module.Basis (Fin d) F E) (u : Fin M × Fin d → AF F) :
    Fin 1 → Fin M → AF F ⊗[F] E :=
  fun _ i => ∑ k, u (i, k) • ((1 : AF F) ⊗ₜ[F] b k)

theorem cv_tupOf {M d : ℕ} (b : Module.Basis (Fin d) F E) (u : Fin M × Fin d → AF F) :
    cv (AF F) b (tupOf b u 0) = u := by
  funext p
  have h : (tupOf b u 0 p.1) = ∑ k, u (p.1, k) • (Algebra.TensorProduct.basis (AF F) b) k := by
    simp only [tupOf, Algebra.TensorProduct.basis_apply]
  simp only [cv]
  rw [h, Module.Basis.repr_sum_self]

theorem tupOf_cv {M d : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin 1 → Fin M → AF F ⊗[F] E) :
    tupOf b (cv (AF F) b (X 0)) = X := by
  funext u i
  obtain rfl : u = 0 := Subsingleton.elim _ _
  simp only [tupOf, cv]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) b).sum_repr (X 0 i)]
  simp only [Algebra.TensorProduct.basis_apply]

end Link

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
