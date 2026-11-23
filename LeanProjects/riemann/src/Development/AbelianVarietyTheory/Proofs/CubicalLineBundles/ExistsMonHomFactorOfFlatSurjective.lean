import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj ComplexOrder in

theorem _root_.GlobalTheory.exists_monHom_factor_of_flat_surjective : ∀ (S : Scheme.{0}) (G G' G'' : Over S) [GrpObj G] [GrpObj G'] [GrpObj G''] (Φ : G ⟶ G') (f : G ⟶ G''), IsMonHom Φ → IsMonHom f → Flat Φ.left → Surjective Φ.left → QuasiCompact Φ.left → (∀ (T : Over S) (x : T ⟶ G), x ≫ Φ = 1 → x ≫ f = 1) → (∃ ψ : G' ⟶ G'', IsMonHom ψ ∧ Φ ≫ ψ = f) ∧ Epi Φ := by
  intro S G G' G'' _ _ _ Φ f hΦ hf hflat hsurj hqc hker
  haveI := hΦ
  haveI := hf
  haveI : EffectiveEpi Φ := _root_.GlobalTheory.CosetQuotient.effectiveEpi_of_left Φ
  haveI : Flat (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.flat_tensorHom Φ Φ
  haveI : Surjective (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.surjective_tensorHom Φ Φ
  haveI : QuasiCompact (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.quasiCompact_tensorHom Φ Φ
  haveI : EffectiveEpi (Φ ⊗ₘ Φ) := _root_.GlobalTheory.CosetQuotient.effectiveEpi_of_left _
  have hcompat : ∀ {Z : Over S} (g₁ g₂ : Z ⟶ G), g₁ ≫ Φ = g₂ ≫ Φ → g₁ ≫ f = g₂ ≫ f := by
    intro Z g₁ g₂ h
    have h1 : (g₁ / g₂) ≫ Φ = 1 := by
      rw [GrpObj.div_comp, h, div_self']
    have h2 := hker Z _ h1
    rwa [GrpObj.div_comp, div_eq_one] at h2
  refine ⟨⟨EffectiveEpi.desc Φ f hcompat, ⟨?_, ?_⟩, EffectiveEpi.fac Φ f hcompat⟩, inferInstance⟩
  · rw [← IsMonHom.one_hom (f := Φ), Category.assoc, EffectiveEpi.fac, IsMonHom.one_hom]
  · rw [← cancel_epi (Φ ⊗ₘ Φ), ← Category.assoc, ← IsMonHom.mul_hom (f := Φ), Category.assoc,
      EffectiveEpi.fac, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, EffectiveEpi.fac]

end GlobalTheory
