import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.CubeModels

theorem model_refine {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π)
    (ρ : Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (h₁ : ρ ≫ pullback.fst _ _ = π)
    (h₂ : ρ ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom φ₁)) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) ρ := by
  obtain ⟨-, l, q, s, sq⟩ := hm
  have hc : Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    subst e
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨ft, inferInstance, inferInstance, inferInstance, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (v₁₃ := f₀) (h₂₂ := Spec.map (CommRingCat.ofHom ψ)) ?_ h₂ (IsPullback.of_hasPullback _ _)
  rw [h₁, ← hc]
  exact sq

def refineMap {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)) :=
  pullback.lift π (f ≫ Spec.map (CommRingCat.ofHom φ₁)) (by
    have hc : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
      subst e
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, ← hc]
    exact hm.2.2.2.2.w)

theorem model_refine' {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) (refineMap e hm) :=
  model_refine e ft hm _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem hasModel_of_spreads : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) →
    GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → GlobalTheory.SpreadingModels.LBSpreads →
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M := by
  intro hS hSm hPr hLB R _ Y f hsm hpr M hM
  obtain ⟨R₀, _, φ, Y₀, f₀, π, hm⟩ := hS R Y f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := hSm R R₀ φ Y Y₀ f f₀ π hm hsm
  have m₁ := model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := hPr R R₁ φ₁ Y _ f _ _ m₁ hpr
  have m₂ := model_refine' e₂ ft₂ m₁
  obtain ⟨R₃, _, ψ₃, φ₃, ρ, e₃, ft₃, r₁, r₂, M₃, hM₃, w, hw⟩ := hLB R R₂ φ₂ Y _ f _ _ m₂ M hM
  have m₃ := model_refine e₃ ft₃ m₂ ρ r₁ r₂
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  refine ⟨R₃, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ R₃, φ₃, _,
    pullback.snd (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) (Spec.map (CommRingCat.ofHom ψ₃)), ρ,
    inferInstance, inferInstance, m₃.2.2.2.2, M₃, hM₃, w, hw⟩

end GlobalTheory.CompanionTheory.CubeModels
