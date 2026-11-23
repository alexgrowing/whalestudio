import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRapoportOfIsUnitDiscr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleEqOfAgreeRapoport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleAllObjOfExtend

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem qExpansionOnAll_of_model (hDP : GlobalTheory.Published.DelignePappasModel) (hQ : GlobalTheory.Published.HilbertQExpansion) :
    QExpansionOnAll := by
  intro F _ _ _ hf e 𝔞 𝔟 k R₀ g a hg ha haR
  obtain ⟨r₀, hr₀, hr₀u⟩ := hQ F hf e 𝔞 𝔟 k R₀ g a hg ha haR
  have hrap : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (X : Obj F (𝔞 * 𝔟⁻¹) (Sp R)), X.IsRapoport := by
    intro R _ _ X
    apply isRapoport_of_isUnit_discr hDP F (𝔞 * 𝔟⁻¹) R
    have h0 : ((NumberField.discr F : ℤ) : R) = algebraMap ℂ R ((NumberField.discr F : ℤ) : ℂ) := by simp
    rw [h0]
    exact (IsUnit.mk0 _ (by exact_mod_cast NumberField.discr_ne_zero F)).map _
  let r₁ : Rule (trivialObjectCondition (𝔞 * 𝔟⁻¹)) ℂ k :=
    { val := fun R _ _ X _ δ ↦ (r₀.extend ℂ).val R X (hrap R X) δ
      homog := fun R _ _ X _ δ δ' c h ↦ (r₀.extend ℂ).homog R X (hrap R X) δ δ' c h
      baseChange := fun R R' _ _ _ _ σ X _ X' _ φ δ δ' h h' ↦
        (r₀.extend ℂ).baseChange R R' σ X (hrap R X) X' (hrap R' X') φ δ δ' h h' }
  obtain ⟨r, hr⟩ := exists_rule_allObj_of_extend hDP F (𝔞 * 𝔟⁻¹) R₀ ℂ Subtype.val_injective k r₀ r₁ (fun R _ _ X hX δ ↦ rfl)
  have hrr : r.HasValues e 𝔞 𝔟 g := by
    intro z hz X _ δ hXz
    rw [hr ℂ X (hrap ℂ X) δ]
    exact hr₀ z hz X (hrap ℂ X) δ hXz
  refine ⟨r, hrr, ?_⟩
  intro s hs
  have hres : ∀ t : Rule (trivialObjectCondition (𝔞 * 𝔟⁻¹)) R₀ k, t.HasValues e 𝔞 𝔟 g →
      (t.restrict (Q' := rapObj (𝔞 * 𝔟⁻¹)) (fun _ _ _ _ ↦ trivial)).HasValues e 𝔞 𝔟 g :=
    fun t ht z hz X _ δ hXz ↦ ht z hz X trivial δ hXz
  have h1 := hr₀u _ (hres s hs)
  have h2 := hr₀u _ (hres r hrr)
  apply rule_eq_of_agree_rapoport hDP F (𝔞 * 𝔟⁻¹) R₀ k s r
  intro R _ _ X hX δ
  exact congrArg (fun t : Rule (rapObj (𝔞 * 𝔟⁻¹)) R₀ k ↦ t.val R X hX δ) (h1.trans h2.symm)

end GlobalTheory.RealMult
