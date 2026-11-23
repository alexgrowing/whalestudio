import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

def winU (bi S η : ℕ) : Finset ℤ := Finset.Icc (bi : ℤ) (bi + S) ∪ Finset.Icc (-(η : ℤ)) η

def TruncationIndexSet (bi S η a : ℕ) : Finset ℤ :=
  ((winU bi S η) ×ˢ (Finset.Icc (1 : ℤ) a)).image fun p => p.1 + p.2

def TruncatedCoefficientPoly (cc : ℤ → O) (bi S η a : ℕ) : O[X] := ∏ m ∈ TruncationIndexSet bi S η a, (X - C (cc m))

def EG (l a S η bi : ℕ) : ℕ :=
  ⌊((3 * a + S + 2 * η : ℝ) - 2) / ((l : ℝ) - 1) + Real.logb l ((bi : ℝ) + η - 1)⌋₊

end Formalism.MainNotions.N.FrobeniusPowerSeries
