import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.ExplicitFunctionSquareIntegrable

noncomputable section

open Finset MeasureTheory Matrix

namespace PositivityTheory.RgDs

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def InCone (abelian₂ η : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b) ∧ η = abelian₂ + ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b

theorem inCone_refl (abelian₂ : Fin n → ℝ) : InCone abelian₂ abelian₂ := ⟨0, by simp, by simp⟩

def KeyFor (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Prop :=
  ∀ S : Submodule ℂ (L2 ε), FiniteDimensional ℂ S → S ≤ Hlam ε Ψ T.w → Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S →
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (e : S →ₗ[ℂ] N) (φ : N),
      (∀ S' : Submodule ℂ (L2 ε), S' ≤ S → Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S' → S' ≠ ⊥ →
        ∃ x : S, (x : L2 ε) ∈ S' ∧ e x ≠ 0) ∧
      (∀ (η : Fin n → ℝ) (x : S), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) η (x : L2 ε) → e x ≠ 0 →
        InCone (lowK ε lam) η) ∧
      ∀ x : S, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) (lowK ε lam) (x : L2 ε) → ∃ c : ℂ, e x = c • φ

def Key : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    S7.IsHCParam lam → S7.IsMu lam μ → IsPsiFor ε lam T (S7.PsiM T μ) → KeyFor ε lam T (S7.PsiM T μ)

def Hilb : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), S7.IsHCParam lam → IsPsiFor ε lam T Ψ → KeyFor ε lam T Ψ →
      Formalism.MainNotions.S.IsDS ε lam (sigLam ε Ψ T.w) ∧
        ∀ (η : Fin n → ℝ) (S : Submodule ℂ (Hlam ε Ψ T.w)), Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ T.w) η S →
          InCone (lowK ε lam) η

end PositivityTheory.RgDs
