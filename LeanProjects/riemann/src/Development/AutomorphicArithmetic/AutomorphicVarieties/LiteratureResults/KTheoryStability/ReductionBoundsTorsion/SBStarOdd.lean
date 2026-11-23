import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStar

noncomputable section

open NumberField NumberField.InfinitePlace UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB

def SWtOdd : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (k : ℕ), Even k →
    ∃ τ : InfinitePlace L → ∀ n : ℕ, Chn (Gm L n) (k + 1) →ₗ[ℝ] ℝ, (∀ w, WSys (𝓞 L) k 1 (τ w)) ∧
      ∀ (N : ℕ) (ω : Form (HS L N) (k + 1)), (∀ g, FInv ω g) →
        ∃ (c : InfinitePlace L → ℝ) (a : ℕ → ∀ n : ℕ, Chn (Gm L n) (k + 1) →ₗ[ℝ] ℝ),
          (∀ j ∈ Finset.Icc 2 (k + 1), WSys (𝓞 L) k j (a j)) ∧
          ∀ z : Chn (Gm L N) (k + 1), IsCyc z →
            ev (emb L N) (intP ω) (one L N) z = ∑ w, c w * τ w N z + ∑ j ∈ Finset.Icc 2 (k + 1), a j N z

def BStarOdd : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ k : ℕ, Even k → k + 1 < nrComplexPlaces L →
    ∀ (l : ℕ) (hl : 0 < l) (n : ℕ), 2 * (k + 1) + 4 ≤ n →
      Module.rank ℤ (Submodule.span ℤ (Set.range fun x : grpH (Gm L n) (k + 1) => zSeq (𝓞 L) hl x k)) ≤
        nrComplexPlaces L

def SBStarOdd : Prop := SChain → SSep → SBridge → SStab → SSurj → SWtOdd → BStarOdd

end PositivityTheory.KB

end
