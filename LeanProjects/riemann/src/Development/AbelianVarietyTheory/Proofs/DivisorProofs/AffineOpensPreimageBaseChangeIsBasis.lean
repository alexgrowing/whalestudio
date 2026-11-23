import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem preAff_basis : ∀ (X₀ X₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) [IsAffineHom pr], (∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U) → (∀ (x : X₁) (U : X₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : X₁) (U : X₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ pr _ hsurj
  refine ⟨?_, ?_⟩
  · intro x U hx
    obtain ⟨V, rfl⟩ := hsurj U
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open (show pr.base x ∈ V from hx) V.isOpen
    exact ⟨Opposite.op ⟨W, hW⟩, hxW, pr.preimage_mono hWV⟩
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨V, rfl⟩ := hsurj U
    have hmem : pr.base x ∈ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := ⟨⟨h₁, h₂⟩, hx⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open hmem (t₁.unop.1 ⊓ t₂.unop.1 ⊓ V).isOpen
    have hWV' : W ≤ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := hWV
    exact ⟨Opposite.op ⟨W, hW⟩, ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₁.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_left) : W ≤ t₁.unop.1))).op⟩,
      ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₂.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_right) : W ≤ t₂.unop.1))).op⟩, hxW,
      pr.preimage_mono (le_trans hWV' inf_le_right)⟩

end GlobalTheory.Obs.BC
