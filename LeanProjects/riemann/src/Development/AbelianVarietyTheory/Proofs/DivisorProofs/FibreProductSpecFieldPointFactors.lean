import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SpecFibreProduct

theorem point_factors (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀)
    (g₂ : R₂ ⟶ R₀) (hP : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁)
    (hg₂ : Function.Surjective g₂) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P) :
    (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨
      (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := by
  have H := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  have hinj : ∀ a b : P, f₁.hom a = f₁.hom b → f₂.hom a = f₂.hom b → a = b :=
    fun a b h₁ h₂ ↦ H.2.1 a b ⟨h₁, h₂⟩
  have hex : ∀ (b : R₁) (c : R₂), g₁.hom b = g₂.hom c → ∃ a : P, f₁.hom a = b ∧ f₂.hom a = c :=
    fun b c h ↦ H.2.2 b c h
  have hs₁ : Function.Surjective f₁.hom := by
    intro b
    obtain ⟨c, hc⟩ := hg₂ (g₁.hom b)
    obtain ⟨a, ha, -⟩ := hex b c hc.symm
    exact ⟨a, ha⟩
  have hs₂ : Function.Surjective f₂.hom := by
    intro c
    obtain ⟨b, hb⟩ := hg₁ (g₂.hom c)
    obtain ⟨a, -, ha⟩ := hex b c hb
    exact ⟨a, ha⟩
  set χ : P ⟶ CommRingCat.of k := Spec.preimage x with hχ
  have hx : Spec.map χ = x := Spec.map_preimage x
  by_cases h : RingHom.ker f₁.hom ≤ RingHom.ker χ.hom
  · left
    let ψ : R₁ →+* k := f₁.hom.liftOfRightInverse (Function.surjInv hs₁)
      (Function.rightInverse_surjInv hs₁) ⟨χ.hom, h⟩
    have hψ : ∀ a, ψ (f₁.hom a) = χ.hom a := fun a ↦
      f₁.hom.liftOfRightInverse_comp_apply _ _ ⟨χ.hom, h⟩ a
    have he : f₁ ≫ CommRingCat.ofHom ψ = χ := CommRingCat.hom_ext (RingHom.ext hψ)
    exact ⟨Spec.map (CommRingCat.ofHom ψ), by rw [← Spec.map_comp, he, hx]⟩
  · right
    have h₂ : RingHom.ker f₂.hom ≤ RingHom.ker χ.hom := by
      intro b hb
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h
      rw [RingHom.mem_ker] at ha hb ⊢
      rw [RingHom.mem_ker] at ha'
      have hab : a * b = 0 := hinj _ _ (by rw [map_mul, ha, zero_mul, map_zero])
        (by rw [map_mul, hb, mul_zero, map_zero])
      have : χ.hom a * χ.hom b = 0 := by rw [← map_mul, hab, map_zero]
      exact (mul_eq_zero.1 this).resolve_left ha'
    let ψ : R₂ →+* k := f₂.hom.liftOfRightInverse (Function.surjInv hs₂)
      (Function.rightInverse_surjInv hs₂) ⟨χ.hom, h₂⟩
    have hψ : ∀ a, ψ (f₂.hom a) = χ.hom a := fun a ↦
      f₂.hom.liftOfRightInverse_comp_apply _ _ ⟨χ.hom, h₂⟩ a
    have he : f₂ ≫ CommRingCat.ofHom ψ = χ := CommRingCat.hom_ext (RingHom.ext hψ)
    exact ⟨Spec.map (CommRingCat.ofHom ψ), by rw [← Spec.map_comp, he, hx]⟩

end GlobalTheory.SpecFibreProduct
