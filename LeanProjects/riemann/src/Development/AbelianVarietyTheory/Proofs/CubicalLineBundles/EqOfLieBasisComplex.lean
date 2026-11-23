import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.DerivZero

theorem exists_lift_isMonHom {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H]
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hG : IsGrpPullback G' G j φ)
    (hH : IsGrpPullback H' H j ψ) (f : G ⟶ H) [IsMonHom f] :
    ∃ f' : G' ⟶ H', IsMonHom f' ∧ f'.left ≫ ψ = φ ≫ f.left := by
  have w : (φ ≫ f.left) ≫ H.hom = G'.hom ≫ j := by
    rw [Category.assoc, Over.w f]
    exact hG.1.w
  obtain ⟨f', hf'⟩ : ∃ f' : G' ⟶ H', f'.left ≫ ψ = φ ≫ f.left :=
    ⟨Over.homMk (hH.1.lift (φ ≫ f.left) G'.hom w) (hH.1.lift_snd _ _ w), hH.1.lift_fst _ _ w⟩
  have hpt : ∀ {T : Over S'} (x : T ⟶ G'), ∃ x₀ : Over.mk (T.hom ≫ j) ⟶ G, x₀.left = x.left ≫ φ := by
    intro T x
    refine ⟨Over.homMk (x.left ≫ φ) ?_, rfl⟩
    dsimp
    rw [Category.assoc, hG.1.w, ← Category.assoc, Over.w x]
  have hmul : ∀ {T : Over S'} (x y : T ⟶ G'), (x * y) ≫ f' = (x ≫ f') * (y ≫ f') := by
    intro T x y
    obtain ⟨x₀, hx₀⟩ := hpt x
    obtain ⟨y₀, hy₀⟩ := hpt y
    apply Over.OverMorphism.ext
    apply hH.1.hom_ext
    · have e1 := hG.2 T x y x₀ y₀ hx₀ hy₀
      have e2 := hH.2 T (x ≫ f') (y ≫ f') (x₀ ≫ f) (y₀ ≫ f)
        (by simp only [Over.comp_left, hx₀, Category.assoc, hf'])
        (by simp only [Over.comp_left, hy₀, Category.assoc, hf'])
      have e3 : (x₀ * y₀) ≫ f = (x₀ ≫ f) * (y₀ ≫ f) := by
        simp [Hom.mul_def]
      rw [← e2, ← e3]
      simp only [Over.comp_left, Category.assoc, hf', e1]
    · simp only [Over.w]
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · have h1 := hmul (1 : 𝟙_ (Over S') ⟶ G') 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ (Over S') ⟶ G') ≫ f' = 1 := by simpa using h1.symm
    simpa [Hom.one_def] using h2
  · have h3 := hmul (fst G' G') (snd G' G')
    simpa [Hom.mul_def] using h3

end GlobalTheory.DerivZero
