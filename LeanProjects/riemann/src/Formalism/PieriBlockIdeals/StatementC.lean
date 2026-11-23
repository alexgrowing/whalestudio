import Formalism.RankGapBounds.LargePrimeFactor

open Real Finset

namespace Formalism.CohomologicalDescent.Cor

open Formalism.RankGapBounds.ChebyshevFactorialBounds

noncomputable section

def DB {ι : Type} (D : Data ι) (τ : ι) : ℤ := D.xlo τ - D.maxB τ

def coefficientBoundTau {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℝ :=
  ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6)
    + (D.ecl τ l : ℝ)
    + (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l)
    + (if ((D.d0 τ l : ℕ) : ℤ) < DB D τ then
        min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0)
    + ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ)))

def BlockIdealBound5 {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → D.lJ < (l : ℝ) → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l →
    D.t + 2 * D.kap l < l →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (coefficientBoundTau D τ l) else (D.ex τ l : ℝ))

def ExactExpStop5 {ι : Type} (D : Data ι) : Prop :=
  ∀ (τ : ι) (l : ℕ), l.Prime → l ∉ D.Exc → D.h + D.Nr < l → D.ex τ l = 0

def ThinStop5 {ι : Type} (D : Data ι) : Prop :=
  ∀ τ : ι, τ ∉ D.T2 → ∀ l : ℕ, l.Prime → l ∉ D.Exc → D.Wthin < l → D.ex τ l = 0

def Inputs5 {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) : Prop :=
  D.ExcCost ∧ D.SumExactBound ∧ D.ExactExpTotal ∧ ExactExpStop5 D ∧ ThinStop5 D ∧ D.CloudRestCut ∧
    D.CloudBound ∧ D.RestBound ∧ BlockIdealBound5 D ∧ D.NoWindowResidue

def rhs5 {ι : Type} [Fintype ι] (D : Data ι) (C : ℝ) : ℝ :=
  (D.Exc.card : ℝ) * D.Kexc
  + ((D.Bad.card : ℝ) * (Fintype.card ι : ℝ) + ((Fintype.card ι : ℝ) - (D.T2.card : ℝ)) * (D.Wthin : ℝ))
      * (D.Nr : ℝ) ^ 2 * Real.log (2 * (D.h : ℝ) + (D.Nr : ℝ))
  + (D.T2.card : ℝ) *
    ( (D.k : ℝ) ^ 2 * ((D.S : ℝ) + (D.k : ℝ)) * Real.log ((D.S : ℝ) + (D.k : ℝ))
      + ((D.eta' : ℝ) + (D.Nr : ℝ)) * ((D.Nr : ℝ) - (D.k : ℝ)) ^ 2
          * Real.log (2 * (D.h : ℝ) + (D.Nr : ℝ))
      + D.lJ * (D.k : ℝ) * ((D.Nr : ℝ) - (D.k : ℝ)) * Real.log (2 * (D.h : ℝ) + (D.Nr : ℝ))
      + (D.k : ℝ) * ((D.S : ℝ) + 1) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
      + (D.k : ℝ) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
      + (D.m : ℝ) * (D.h : ℝ) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
          * (1 + Real.log ((D.h : ℝ) + (D.Nr : ℝ)))
      + C * ( (D.m : ℝ) * ((D.h : ℝ) + (D.Nr : ℝ)) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
          + (D.k : ℝ) * (D.S : ℝ) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
          + (D.m : ℝ) * (D.h : ℝ) * (1 + Real.log (D.h : ℝ)) * Real.log ((D.h : ℝ) + (D.Nr : ℝ)) ) )

def Corollary5 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), Inputs5 D → D.Params →
      ∀ X : ℕ, ∑ l ∈ primesUpTo X, (D.J l : ℝ) * Real.log (l : ℝ) ≤ rhs5 D C

end

end Formalism.CohomologicalDescent.Cor
