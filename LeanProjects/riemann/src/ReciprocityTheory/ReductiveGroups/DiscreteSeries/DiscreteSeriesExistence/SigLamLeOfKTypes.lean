import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CvAEquivariantA

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def opConv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (v : H) : H :=
  ∫ g : Formalism.REAL.UJ ε, α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) v ∂(Formalism.REAL.muG ε)

def IsAdKInv (ε : Fin n → Bool) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ k ∈ Kset ε, ∀ g, α (k * g * star k) = α g

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_le_of_kTypes (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (W : Submodule ℂ (Hlam ε Ψ v₀)) (hWf : FiniteDimensional ℂ W)
    (hWfull : ∀ (μ : Fin n → ℝ) (S : Submodule ℂ (Hlam ε Ψ v₀)),
      Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S →
        (∃ S' ≤ W, Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S') → S ≤ W)
    (hWsum : W ≤ sSup {S : Submodule ℂ (Hlam ε Ψ v₀) | ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S})
    (U : Set (Matrix (Fin n) (Fin n) ℂ)) (hU : IsOpen U) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) :
    ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U ∧
      IsAdKInv ε α ∧ ∀ w ∈ W, opConv ε (sigLam ε Ψ v₀) α w = w := by
  obtain ⟨α, ⟨hsmooth, hcpt, hsupp, hinv⟩, hfix⟩ :=
    exists_cvA_idA (sigLam_isURepOn hgap hP hv₀) (sigLam_admissible hgap hP hv₀) W hWf hWsum hU h1
  exact ⟨α, hsmooth, hcpt, hsupp, fun k hk g => hinv k hk g, hfix⟩

end ReciprocityTheory.ChartRestriction.DS
