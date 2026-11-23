import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreIncomp
import GroundTheory.HeightsAndTheta.Heights.Intersections.OneNotMemOfIsPrime
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem semiLocRing_le_locRing (P : Ideal (MRing ι)) {𝒲 : Set (Ideal (MRing ι))} {W : Ideal (MRing ι)}
    (hW : W ∈ 𝒲) : semiLocRing P 𝒲 ≤ locRing P W := by
  unfold semiLocRing locRing
  refine Subring.closure_mono ?_
  rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
  exact ⟨u, w, a, hw, hwW W hW, hu, hwa, rfl⟩

def semiToLoc (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲) :
    semiLocRing P 𝒲 →+* locRing P W :=
  Subring.inclusion (semiLocRing_le_locRing P hW)

theorem semiToLoc_coe (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    (b : semiLocRing P 𝒲) : ((semiToLoc P 𝒲 W hW b : locRing P W) : FractionRing (MRing ι ⧸ P)) = b := by
  simp [semiToLoc]

def semiMaxIdeal (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    [IsLocalRing (locRing P W)] : Ideal (semiLocRing P 𝒲) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (semiToLoc P 𝒲 W hW)

instance semiMaxIdeal.isPrime (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    [IsLocalRing (locRing P W)] : (semiMaxIdeal P 𝒲 W hW).IsPrime :=
  Ideal.comap_isPrime _ _

end Objects

def SemilocMaxIdeals.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)),
    IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')],
      (semiMaxIdeal P' (fibreOver v P' W) W' hW').IsMaximal ∧
      letI := (semiToLoc P' (fibreOver v P' W) W' hW').toAlgebra
      IsLocalization.AtPrime (locRing P' W') (semiMaxIdeal P' (fibreOver v P' W) W' hW')) ∧
    (∀ (W₁ W₂ : Ideal (MRing ι')) (h₁ : W₁ ∈ fibreOver v P' W) (h₂ : W₂ ∈ fibreOver v P' W)
      [IsLocalRing (locRing P' W₁)] [IsLocalRing (locRing P' W₂)],
      semiMaxIdeal P' (fibreOver v P' W) W₁ h₁ = semiMaxIdeal P' (fibreOver v P' W) W₂ h₂ → W₁ = W₂) ∧
    ∀ M : Ideal (semiLocRing P' (fibreOver v P' W)), M.IsMaximal →
      ∃ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W), ∀ [IsLocalRing (locRing P' W')],
        M = semiMaxIdeal P' (fibreOver v P' W) W' hW'

end GroundTheory.Heights₂.Heights.Inter
