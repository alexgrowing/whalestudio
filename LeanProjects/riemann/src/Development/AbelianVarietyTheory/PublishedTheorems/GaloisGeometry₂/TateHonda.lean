import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum

namespace GlobalTheory.Published

open ReciprocityTheory.ChartRestriction.G.Semi in

def TateHonda : Prop :=
  ∀ (k Ω : Type) [Field k] [Finite k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (φ : Ω ≃ₐ[k] Ω), (∀ x, φ x = x ^ Nat.card k) →
    (∀ (l : ℕ) [Fact l.Prime], (l : k) ≠ 0 → ∀ (A B : Over (Spec (CommRingCat.of k))) [GrpObj A] [GrpObj B]
      [IsAbelianScheme A] [IsAbelianScheme B],
      (∀ f : H ℚ_[l] 1 (geom Ω B.hom) →ₗ[ℚ_[l]] H ℚ_[l] 1 (geom Ω A.hom),
        (∀ σ, f ∘ₗ gal ℚ_[l] Ω B.hom 1 σ = gal ℚ_[l] Ω A.hom 1 σ ∘ₗ f) →
        f ∈ Submodule.span ℚ_[l] {g | ∃ u : A ⟶ B, IsMonHom u ∧ g = pull ℚ_[l] 1 (geomMap Ω A.hom u.left (Over.w u))}) ∧
      ∀ [Module.Finite ℚ_[l] (H ℚ_[l] 1 (geom Ω A.hom))] [Module.Finite ℚ_[l] (H ℚ_[l] 1 (geom Ω B.hom))],
        (gal ℚ_[l] Ω A.hom 1 φ⁻¹).charpoly = (gal ℚ_[l] Ω B.hom 1 φ⁻¹).charpoly →
        ∃ u : A ⟶ B, IsMonHom u ∧ IsFinite u.left ∧ Surjective u.left) ∧
    ∀ P : Polynomial ℤ, P.Monic → Irreducible P → (∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ ^ 2 = (Nat.card k : ℝ)) →
      ∃ (A : Over (Spec (CommRingCat.of k))) (_ : GrpObj A) (_ : IsAbelianScheme A) (e : ℕ), 1 ≤ e ∧
        ∀ (l : ℕ) [Fact l.Prime], (l : k) ≠ 0 → ∀ [Module.Finite ℚ_[l] (H ℚ_[l] 1 (geom Ω A.hom))],
          (gal ℚ_[l] Ω A.hom 1 φ⁻¹).charpoly = (P ^ e).map (Int.castRingHom ℚ_[l])

end GlobalTheory.Published

end
