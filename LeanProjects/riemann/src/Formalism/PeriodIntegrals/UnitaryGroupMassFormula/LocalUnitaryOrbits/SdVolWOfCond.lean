import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRSmulF

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

def CondAllF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem condV_of_all (h : CondAllF) : CondV σ J ψ v := by
  intro hs t
  rw [← h F hs.1.1 ψ hs.2.2.1 hs.2.2.2 v t]
  exact forall₂_congr fun s _ => by rw [mul_comm]

theorem sdVolW_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) : SdVolW σ J ψ v Λ a := by
  intro hS
  exact sdVolW_of_pi σ J ψ v Λ a (condV_of_all σ J ψ v hC) (dualW_of_perf σ J ψ v Λ a hP)
    (idxPiW_std σ J ψ v Λ a hS) hS

theorem sdVolH_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) :
    SdVolH σ J ψ v a := by
  intro hS
  exact sdVolH_of_pi σ J ψ v a (condV_of_all σ J ψ v hC) (dualH_of_perf σ J ψ v a hP)
    (idxPiH_std σ J ψ v a hS) hS

end PI.OmLocU.SdB
