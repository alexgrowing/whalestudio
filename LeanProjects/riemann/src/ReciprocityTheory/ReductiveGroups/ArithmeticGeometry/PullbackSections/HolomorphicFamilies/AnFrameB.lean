import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (ε : K → ℤ)
  {N : ℕ} (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z))

def IsFrameFam (fr : K → L.ι → (Fin N → ℂ) → ℂ) : Prop :=
  ∀ k, (∀ i, DifferentiableOn ℂ (fr k i) {z | ⊤ ≤ (q z ≫ φ k) ⁻¹ᵁ L.U i}) ∧
    (∀ i z, ⊤ ≤ (q z ≫ φ k) ⁻¹ᵁ L.U i → fr k i z ≠ 0) ∧
    (∀ i i' z, ⊤ ≤ (q z ≫ φ k) ⁻¹ᵁ (L.U i ⊓ L.U i') →
      fr k i z = valAt' (q z ≫ φ k) (L.U i ⊓ L.U i') (L.g i i').val * fr k i' z)

def evidence (t : LB.Gen (LB.LinComb L φ ε)) (fr : K → L.ι → (Fin N → ℂ) → ℂ) (j : K → L.ι)
    (z : Fin N → ℂ) : ℂ :=
  valAt' (q z) (LB.wchart L φ j) (t.s j).val * ∏ k, fr k (j k) z ^ (-ε k)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
