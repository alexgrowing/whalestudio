import Mathlib
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

theorem exists_affineOpen_nhds_le {X : Scheme.{0}} (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (W : Set X) from hx) W.isOpen
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

theorem pairBC_fst_basis : ∀ (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (e : f₁ ≫ pr = pr' ≫ f₀), (∀ U : Y₁.Opens, ∃ V : Y₀.Opens, pr' ⁻¹ᵁ V = U) → (∀ (x : Y₁) (U : Y₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : Y₁) (U : Y₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ Y₀ Y₁ pr pr' _ _ f₀ f₁ e hsurj
  constructor
  · intro x U hx
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    obtain ⟨V, hfV, -⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) ⊤ trivial
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x) (W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨hy, hfV⟩
    refine ⟨Opposite.op (⟨(U', V), hU'le.trans inf_le_right⟩ : Pair f₀), ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans inf_le_left)
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    have hy₁ : pr' x ∈ t₁.unop.1.1.1 := h₁
    have hy₂ : pr' x ∈ t₂.unop.1.1.1 := h₂
    have hf₁ : f₀ (pr' x) ∈ t₁.unop.1.2.1 := t₁.unop.2 hy₁
    have hf₂ : f₀ (pr' x) ∈ t₂.unop.1.2.1 := t₂.unop.2 hy₂
    obtain ⟨V, hfV, hVle⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) (t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨hf₁, hf₂⟩
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x)
      (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1 ⊓ W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨⟨⟨hy₁, hy₂⟩, hy⟩, hfV⟩
    let p : Pair f₀ := ⟨(U', V), hU'le.trans inf_le_right⟩
    have hp₁ : p ≤ t₁.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)), hVle.trans inf_le_left⟩)
    have hp₂ : p ≤ t₂.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)), hVle.trans inf_le_right⟩)
    refine ⟨Opposite.op p, ⟨(homOfLE hp₁).op⟩, ⟨(homOfLE hp₂).op⟩, ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans (inf_le_left.trans inf_le_right))

end GlobalTheory.Obs.BC
