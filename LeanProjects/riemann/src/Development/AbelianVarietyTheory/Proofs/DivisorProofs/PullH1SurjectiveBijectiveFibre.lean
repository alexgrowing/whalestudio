import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_bijective : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  intro R k _ _ σ hσ X s X₀ s₀ ψ w
  let e : R ≃+* k := RingEquiv.ofBijective σ hσ
  let τ : k →+* R := e.symm.toRingHom
  have hστ : ∀ r, σ (τ r) = r := fun r => e.apply_symm_apply r
  have hτσ : ∀ r, τ (σ r) = r := fun r => e.symm_apply_apply r
  have c1 : spMap τ ≫ spMap σ = 𝟙 (Sp R) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : σ.comp τ = RingHom.id k := RingHom.ext hστ
    have : τ.comp σ = RingHom.id R := RingHom.ext hτσ
    rw [this]; simp
  have c2 : spMap σ ≫ spMap τ = 𝟙 (Sp k) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : σ.comp τ = RingHom.id k := RingHom.ext hστ
    rw [this]; simp
  let l : X ⟶ X₀ := w.lift (𝟙 X) (s ≫ spMap τ) (by rw [Category.id_comp, Category.assoc, c1, Category.comp_id])
  have hl1 : l ≫ ψ = 𝟙 X := w.lift_fst _ _ _
  have hl2 : l ≫ s₀ = s ≫ spMap τ := w.lift_snd _ _ _
  have hl3 : ψ ≫ l = 𝟙 X₀ := by
    apply w.hom_ext
    · rw [Category.assoc, hl1, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hl2, ← Category.assoc, w.w, Category.assoc, c2, Category.comp_id, Category.id_comp]
  obtain ⟨hcomp, -, hid⟩ := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  intro b
  refine ⟨pullHO1 hl2 b, ?_⟩
  have := (hcomp k R X₀ X s₀ s τ l hl2 k X₀ s₀ σ ψ w.w (RingHom.id k) (𝟙 (Over.mk s₀) : Over.mk s₀ ⟶ Over.mk s₀).left
    (ovw (𝟙 (Over.mk s₀))) (by simp [hl3]) (fun r => (hστ r).symm)).1 b
  rw [this]
  exact (hid k (Over.mk s₀)).1 b

end GlobalTheory.AbCoh
