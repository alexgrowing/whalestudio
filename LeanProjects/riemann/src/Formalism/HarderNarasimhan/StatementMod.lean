import Mathlib
import Formalism.HarderNarasimhan.StatementPl

open Module NumberField

noncomputable section

namespace Formalism.HN

def IdealScale : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), I ≠ 0 →
    ∀ M : Submodule (𝓞 K) V, M.FG → M ≠ ⊥ →
      (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M).FG ∧
      muDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muMaxDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muMaxDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muMinDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muMinDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)

def IndexMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ M N : Submodule (𝓞 K) V, M.FG → N ≤ M → N ≠ ⊥ → rkK N = rkK M →
      muDef b X N = muDef b X M -
        2 * Real.log (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) /
          ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) ∧
      muMaxDef b X N ≤ muMaxDef b X M

def CutLattice : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), I ≠ 0 →
    ∀ M N' : Submodule (𝓞 K) V, M.FG → M ≠ ⊥ → N' ≤ Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M →
      N' ≠ ⊥ → rkK N' = rkK M →
      muMaxDef b X N' ≤ muMaxDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muDef b X N' = muDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) -
        2 * Real.log (N'.toAddSubgroup.relIndex
          (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M).toAddSubgroup : ℝ) /
          ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ))

def LcvFormula : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V) (M : Submodule (𝓞 K) V), LinearIndependent K e → M.FG → M ≠ ⊥ →
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e) →
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M)).Finite ∧
      muDef b X M = -((1 / (nPl K : ℝ)) * ∑ v, Real.log (gramPl b X v e).det.re +
        2 * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
          (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
            (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ))) /
        (rkK M : ℝ)

end Formalism.HN
