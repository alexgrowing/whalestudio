import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaFA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure

noncomputable section

open Finset Matrix MeasureTheory

namespace CompanionTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

def V1 {n : ℕ} (ε : Fin n → Bool) {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Submodule ℂ (L2 ε) :=
  (datumV ε Ψ T.w).map (smD ε (rreg ε)).subtype

def StepStable : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      ∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w

def StepDatum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ)

def StepMoll : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W S : Submodule ℂ (L2 ε)), IsClosed (W : Set (L2 ε)) →
    (∀ g ∈ UJset ε, ∀ x ∈ W, rreg ε g x ∈ W) → FiniteDimensional ℂ S → S ≤ W →
      Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S →
      ∃ A : L2 ε →ₗ[ℂ] L2 ε, (∀ k ∈ Kset ε, ∀ x, A (rreg ε k x) = rreg ε k (A x)) ∧
        (∀ x ∈ S, A x = 0 → x = 0) ∧ S.map A ≤ smD ε (rreg ε) ∧ S.map A ≤ W

def StepWtSpan : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (S : Submodule ℂ (L2 ε)), FiniteDimensional ℂ S → S ≤ smD ε (rreg ε) →
    Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (e : S →ₗ[ℂ] N), e ≠ 0 →
      ∃ (ν : Fin n → ℝ) (x : S), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) ν (x : L2 ε) ∧ e x ≠ 0

def StepCone : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), S7.IsHCParam lam → IsPsiFor ε lam T Ψ →
      KeyFor ε lam T Ψ → ∀ (η : Fin n → ℝ) (S : Submodule ℂ (L2 ε)), S ≤ Hlam ε Ψ T.w →
        Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) η S → InCone (lowK ε lam) η

def StepLowEq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), S7.IsHCParam lam → IsPsiFor ε lam T Ψ →
      KeyFor ε lam T Ψ → ∀ S : Submodule ℂ (L2 ε), S ≤ Hlam ε Ψ T.w →
        Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) S → S = V1 ε Ψ

def StepIrred : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      (∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w) →
      (∀ S : Submodule ℂ (L2 ε), S ≤ Hlam ε Ψ T.w →
        Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) S → S = V1 ε Ψ) →
      ∀ W : Submodule ℂ (L2 ε), W ≤ Hlam ε Ψ T.w → IsClosed (W : Set (L2 ε)) →
        (∀ g ∈ UJset ε, ∀ x ∈ W, rreg ε g x ∈ W) → W = ⊥ ∨ W = Hlam ε Ψ T.w

def StepFormulaF : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      (∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w) →
      (∀ S : Submodule ℂ (L2 ε), S ≤ Hlam ε Ψ T.w →
        Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) S → S = V1 ε Ψ) →
      ∀ g ∈ UJset ε, ∀ v v' : T.V,
        inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
          ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v)

def StepVogan : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam η : Fin n → ℝ), S7.IsHCParam lam → InCone (lowK ε lam) η →
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε η

end CompanionTheory.RgDs.Hilb
