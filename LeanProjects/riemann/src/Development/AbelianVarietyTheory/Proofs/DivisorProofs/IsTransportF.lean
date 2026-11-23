import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsTransportF (σ : E →ₐ[F] E) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (ψ : AddChar (AF F) ℂ) {ξ : AF F ⊗[F] E} {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {κ : Type} [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (ω : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ))
    (om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)) : Prop :=
  ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)) (g : GAF σ JS) (h : GAF σ JT),
    mtF σ JT h = a.1.1 → mtF σ JS g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ schA F κ, om (a, b) Φ ∈ schA F κ ∧ thetaTr F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr F co ψ Φ)

end GlobalTheory.WeilSchrodinger

end
