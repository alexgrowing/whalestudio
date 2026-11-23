import Mathlib

noncomputable section

open NumberField

namespace Formalism.NormVectorIdentities.Items

section abelian₂

variable {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

def vecS (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  fun i => v.embedding (b.repr x i)

def fcoordS (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  Matrix.mulVec (X v)⁻¹ (vecS b v x)

def cnormS (u : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖u i‖ ^ 2)

def normS (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) : ℝ :=
  cnormS (fcoordS b X v x)

variable (K) in

def nPlS : ℕ := Fintype.card (InfinitePlace K)

end abelian₂

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}

def meanLogS (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) : ℝ :=
  (1 / (nPlS K : ℝ)) * ∑ v, Real.log (normS (Pi.basisFun K (Fin n)) X v x ^ 2)

def LamS (M : Submodule (𝓞 K) (Fin n → K)) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (La : ℝ) : Prop :=
  ∀ x ∈ M, x ≠ 0 → -(2 * La) ≤ meanLogS X x

end Formalism.NormVectorIdentities.Items
