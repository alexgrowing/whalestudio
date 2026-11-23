import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkSpecializesCompatRingMap
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.StalkField

theorem exists_stalk_field_hom : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (p : Sp Ω ⟶ X), (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ φ : X.presheaf.stalk (p.base (genericPoint (Sp Ω))) →+* Ω, φ.Finite ∧ ∀ (K : Type) [Field K] (τ₁ τ₂ : Ω →+* K), spMap τ₁ ≫ p = spMap τ₂ ≫ p → τ₁.comp φ = τ₂.comp φ := by
  intro Ω _ X p hfin
  have hpt : genericPoint (Sp Ω) = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  rw [hpt] at hfin ⊢
  refine ⟨(Scheme.stalkClosedPointTo p).hom, ?_, ?_⟩
  · have e : Scheme.stalkClosedPointTo p = p.stalkMap _ ≫ (stalkClosedPointIso (CommRingCat.of Ω)).hom := rfl
    rw [e, CommRingCat.hom_comp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of Ω)).hom).2) hfin
  · intro K _ τ₁ τ₂ h
    have hs : ∀ τ : Ω →+* K, (spMap τ ≫ p) (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω) := by
      intro τ
      apply specializes_of_eq
      exact congrArg p (Subsingleton.elim ((spMap τ).base (IsLocalRing.closedPoint K)) (IsLocalRing.closedPoint Ω))
    have H : ∀ (q₁ q₂ : Sp K ⟶ X), q₁ = q₂ → ∀ (h₁ : q₁ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω))
        (h₂ : q₂ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω)) a,
        (Scheme.stalkClosedPointTo q₁).hom ((X.presheaf.stalkSpecializes h₁).hom a) =
          (Scheme.stalkClosedPointTo q₂).hom ((X.presheaf.stalkSpecializes h₂).hom a) := by
      rintro _ _ rfl _ _ _; rfl
    ext a
    simp only [RingHom.comp_apply]
    rw [← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₁ (hs τ₁) a,
      ← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₂ (hs τ₂) a]
    exact H _ _ h _ _ a

end GlobalTheory.StalkField
