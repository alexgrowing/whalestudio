import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatD

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hRatF (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : Matrix (Fin nT) (Fin nS) E) : E :=
  ∑ a, ∑ b, ∑ c, ∑ d, JS⁻¹ a b * σ (y c b) * JT c d * x d a

structure GoodLat {nS nT : ℕ} (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : Prop where
  fg : Λ.FG
  den : ∀ M : Matrix (Fin nT) (Fin nS) E, ∃ N : ℕ, 0 < N ∧ N • M ∈ Λ

def RatSD (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : Prop :=
  ∀ M, M ∈ Λ ↔ ∀ M' ∈ Λ, ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT M M') = n

end PositivityTheory.ThKW

end
