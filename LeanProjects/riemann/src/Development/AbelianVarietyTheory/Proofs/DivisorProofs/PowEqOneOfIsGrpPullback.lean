import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexBaseChangePolarizedAbelianFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFineModuliAtComplexEmbeddingComplexBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfComplexBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfMarkedPeriodsFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem pow_eq_one_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (hG : IsGrpPullback G' G f φ) (e : 𝟙_ (Over S) ⟶ G)
    (e' : 𝟙_ (Over S') ⟶ G') (h : e'.left ≫ φ = f ≫ e.left) (N : ℕ) (hN : e ^ N = 1) : e' ^ N = 1 := by
  let T : Over S' := 𝟙_ (Over S')
  let ψ : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      rw [Category.assoc, hG.1.w, ← Category.assoc, Over.w x]; rfl)
  have hψ : ∀ x y, ψ (x * y) = ψ x * ψ y := fun x y => by
    ext1
    exact (hG.2 T x y (ψ x) (ψ y) rfl rfl).symm
  let Ψ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' ψ hψ
  have inj : Function.Injective ψ := fun x y hxy => by
    ext1
    apply hG.1.hom_ext
    · exact congrArg CommaMorphism.left hxy
    · rw [Over.w x, Over.w y]
  have h1 : ψ e' = toUnit _ ≫ e := by
    ext1
    simp only [ψ, Over.homMk_left, Over.comp_left, h]
    congr 1
  apply inj
  have : Ψ (e' ^ N) = Ψ 1 := by
    rw [map_pow, map_one]
    show (ψ e') ^ N = 1
    rw [h1, ← comp_pow, hN, comp_one]
  exact this

end GlobalTheory.PELU

namespace GlobalTheory.PELU

theorem nonempty_unif : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 3 ≤ N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → (∀ D' t, C D' t → FullMark N D' t) → FineAt F σ ρ N C → Nonempty (Unif F σ ρ N C) := by
  intro O _ bar g ρ R _ σ Λ F N C d hN heta hsm hqc hfull hfine
  obtain ⟨F', hbc⟩ := GlobalTheory.T.exists_complexBaseChange_polarizedAbelianFamily O g R σ Λ F
  obtain ⟨f, φ, hX, hA, -, -, heta'⟩ := id hbc
  have e' : ∀ a, F'.eta a ^ N = 1 := fun a =>
    pow_eq_one_of_isGrpPullback f φ hA (F.eta a) (F'.eta a) (heta' a) N (heta a)
  have s' : SmoothOfRelativeDimension d F'.s :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback hX hsm
  have q' : QuasiCompact F'.s := MorphismProperty.of_isPullback hX hqc
  exact GlobalTheory.T.complexUniformisation_of_complexBaseChange O bar g ρ R σ Λ F N C F' hbc
    (GlobalTheory.T.complexUniformisation_of_markedPeriods_family O bar g ρ Λ F' N C d hN e' s' q' hfull (GlobalTheory.T.isFineModuliAtComplexEmbedding_complexBaseChange O bar g ρ R σ Λ F N C F' hbc hfine))

end GlobalTheory.PELU
