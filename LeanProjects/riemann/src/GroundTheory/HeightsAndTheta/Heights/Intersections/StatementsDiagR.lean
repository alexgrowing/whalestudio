import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

abbrev ProjectiveLineBundle.Diag {D : ℕ} (S : ProjectiveLineBundle D) : Ideal (MRing S.WIdx) :=
  T.wwIdeal S.x S.δ S.e S.φ (S.a 0) (S.a 0)

section Statements

def DiagDiv.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.DiagDivStatement (Φ := Φ) B e φ δ

def DiagPullI.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X : HermLine S.YIdx) (X₀ X₁ : HermLine S.WIdx)
    (L : Fin D → HermLine S.WIdx),
    IsSmoothHerm X → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ → IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ →
    (∀ j, IsSmoothHerm (L j)) →
    I T.WBlk S.WIdx S.Diag (D + 1) (Fin.snoc L X₀) = I T.WBlk S.WIdx S.Diag (D + 1) (Fin.snoc L X₁)

def ZeroSetNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (s : MRing ι)
    (a : K → ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsMultiHomog s a → s ∉ P →
    (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) s) ≠ 0 → g₁ z = g₂ z) →
    ptsIntegral P φ g₁ = ptsIntegral P φ g₂

end Statements

section Inhabit

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
