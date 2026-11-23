import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

def DimLtStatement : Prop :=
  ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (V W : Ideal (MvPolynomial σ F)),
    V.IsPrime → W.IsPrime → V < W →
    ringKrullDim (MvPolynomial σ F ⧸ W) < ringKrullDim (MvPolynomial σ F ⧸ V)

def DimPITStatement : Prop :=
  ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (V W : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F),
    V.IsPrime → s ∉ V → W ∈ (V ⊔ Ideal.span {s}).minimalPrimes →
    ringKrullDim (MvPolynomial σ F ⧸ W) + 1 = ringKrullDim (MvPolynomial σ F ⧸ V)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
