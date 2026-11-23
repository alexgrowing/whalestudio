import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelEps

def EpsilonConsistency : Prop :=
  ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion K) Circle), Continuous ψ → ψ ≠ 1 →
    ∀ l : List (BTerm h ψ), (∀ σ : Weil h, (l.map fun t => (t.n : ℂ) * (trW t.indChi σ - trW t.indOne σ)).sum = 0) →
      val l = 1

def EpsilonConsistencyFiniteOrder : Prop :=
  ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion K) Circle), Continuous ψ → ψ ≠ 1 →
    ∀ l : List (BTerm h ψ), (∀ t ∈ l, ∃ N : ℕ, 0 < N ∧ t.χ ^ N = 1) →
      (∀ σ : Weil h, (l.map fun t => (t.n : ℂ) * (trW t.indChi σ - trW t.indOne σ)).sum = 0) → val l = 1

end GlobalTheory.DelEps

end
