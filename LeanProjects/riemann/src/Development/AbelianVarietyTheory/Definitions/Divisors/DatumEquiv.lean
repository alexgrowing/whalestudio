import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def PolyOnK (ε : Fin n → Bool) (f : Mat n → ℂ) : Prop := ∃ P : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, f k = ev k P

def trK {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : Mat n → (W →L[ℂ] W)) (k : Mat n) : ℂ :=
  LinearMap.trace ℂ W (T k : W →ₗ[ℂ] W)

def IsKIrr (ε : Fin n → Bool) (γ : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (T : Mat n → (W →L[ℂ] W)) : Prop :=
  Nontrivial W ∧ Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T ∧ Formalism.MainNotions.S.IsKTypeOf ε T γ ⊤

abbrev dD (ε : Fin n → Bool) {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    Module.End ℂ (TensorProduct ℂ M (Fock n)) := dOp ε (eT E) cpT + dOp' ε (eT E) cmT

abbrev tor (θ : Fin n → ℝ) : Fin n → ℂ := fun a => Complex.exp (θ a * Complex.I)

def BlockForm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ (M : ℕ) (Q : Poly n), Q ∈ blockAlg ε ∧
    ∀ k ∈ Formalism.REAL.Kset ε, ev k P = ev k (detbP n ^ M * Q)

def CoefPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    ∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ

def TrPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) → PolyOnK ε fun k => conj (trK T k)

def AvgMap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)) (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]
    (S : Mat n → (Z →L[ℂ] Z)) (Γ : Z →ₗ[ℂ] Z), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S →
    ∫ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) ∂(muK ε) ≠ 0 →
    ∃ Φ : W →ₗ[ℂ] Z, Φ ≠ 0 ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = S k (Φ v)

def SchurOne : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    ∫ k : KG ε, conj (trK T (toMK k)) * trK T (toMK k) ∂(muK ε) = 1

def SumTypes : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S →
    Formalism.MainNotions.S.IsKStableOn ε σ S → S ≤ sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'}

def PolyAvg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
      IsURepOn (UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧
        (∀ P : Poly n, P.totalDegree ≤ d → ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ S) ∧
        ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A

def DatumEquiv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StdGap ε lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
    IsURepOn (UJset ε) σ → Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) (lowK ε lam) V → V ≠ ⊥ →
    (∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
    ∃ U : H ≃ₗᵢ[ℂ] X, ∀ g ∈ UJset ε, ∀ x, U (σ g x) = D g (U x)

def MatRep : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)),
    IsUnitaryRep π → IsTopIrreducible π → ∃ σ : Mat n → (U →L[ℂ] U), IsURepOn (UJset ε) σ ∧
      Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ ∧ ∀ g : UJ ε, σ (toM g) = π g

end GlobalTheory.PsCo.PcEF
