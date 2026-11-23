import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyPolAVStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueHomOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeSurjectiveOfOntoComplexPoints
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_isGrpPullback_polAV (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), P'.g = P.g ∧ IsGrpPullback P'.A P.A f φ := by
  obtain ⟨P', g, hg, hd, hm, -⟩ := hB S S' f P
  refine ⟨P', g, hd, hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have ex : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
  have ey : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
  rw [ex, ey, ← hm]
  rfl

theorem IsGrpPullback.id_pow_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (N : ℕ) :
    (𝟙 G' ^ N).left ≫ φ = φ ≫ (𝟙 G ^ N).left := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h G'
  have h1 : (E (𝟙 G')).left = φ := by rw [hE]; exact Category.id_comp _
  have h2 : E (𝟙 G' ^ N) = E (𝟙 G') ≫ 𝟙 G ^ N := by
    rw [map_pow, MonObj.comp_pow, Category.comp_id]
  rw [← hE, h2, Over.comp_left, h1]

theorem exists_inverse_isogeny_ringOfIntegers :
    ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp (𝓞 K))) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P'.A, ∃ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, y = x ≫ Φ) → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  intro hT hL hE K _ _ σ P P' Φ hg hΦ honto
  obtain ⟨Q, φ, hQ, hφ⟩ := exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) P
  obtain ⟨Q', φ', hQ', hφ'⟩ := exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) P'
  obtain ⟨⟨Φ₀, hΦ₀, -⟩, hmon⟩ := existsUnique_hom_of_isGrpPullback _ _ _ P.A P'.A Q.A Q'.A φ φ' hφ hφ' Φ
  have hm₀ : IsMonHom Φ₀ := hmon Φ₀ hΦ₀ hΦ
  have hs : Surjective Φ.left :=
    (GlobalTheory.OntoSurj.surjective_of_onto_complex_points (𝓞 K) (σ.comp (algebraMap (𝓞 K) K))
      (σ.injective.comp (IsFractionRing.injective (𝓞 K) K)) P'.A P.A Φ P'.isAb P.isAb honto).1
  have hpb : IsPullback φ Φ₀.left Φ.left φ' := by
    refine IsPullback.of_bot ?_ hΦ₀.symm hφ'.1
    rw [Over.w Φ₀, Over.w Φ]
    exact hφ.1
  have hs₀ : Surjective Φ₀.left := MorphismProperty.of_isPullback (P := @Surjective) hpb hs
  obtain ⟨N, ψ₀, hN, hψ₀, e₁, e₂⟩ := GlobalTheory.T.exists_inverse_isogeny_of_surjective_polAV hT hL K σ Q Q' Φ₀ (hQ.trans (hg.trans hQ'.symm)) hm₀ hs₀
  obtain ⟨ψ, hψ, eψ, -⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P'.A P.A Q'.A Q.A φ' φ
    P'.isAb P.isAb hφ' hφ ψ₀ hψ₀
  refine ⟨N, ψ, hN, hψ, ?_, ?_⟩
  · obtain ⟨F, -, -, hF⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P.A P.A Q.A Q.A φ φ
      P.isAb P.isAb hφ hφ (Φ₀ ≫ ψ₀) inferInstance
    refine (hF _ ?_).trans (hF _ ?_).symm
    · rw [Over.comp_left, Over.comp_left, Category.assoc, eψ, ← Category.assoc, hΦ₀, Category.assoc]
    · rw [e₁]; exact IsGrpPullback.id_pow_left hφ N
  · obtain ⟨F, -, -, hF⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P'.A P'.A Q'.A Q'.A φ' φ'
      P'.isAb P'.isAb hφ' hφ' (ψ₀ ≫ Φ₀) inferInstance
    refine (hF _ ?_).trans (hF _ ?_).symm
    · rw [Over.comp_left, Over.comp_left, Category.assoc, hΦ₀, ← Category.assoc, eψ, Category.assoc]
    · rw [e₂]; exact IsGrpPullback.id_pow_left hφ' N

end GlobalTheory.LamF
