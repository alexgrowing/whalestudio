import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolModelIso

theorem exists_iso_of_isPol : PolMapSt → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    (Z : Model Xo c β) (Z' : Model Xo c β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X) (φ : InvFun (𝓞 E))
    (m : ℕ) (b : O →+* O') (b' : O' →+* O), Models.IsDedFrac β → Models.IsDedFrac β' → Algebra.FiniteType ℤ O →
    Algebra.FiniteType ℤ O' → IsTwInv H φ → β'.comp b = β → β.comp b' = β' → IsPol φ m Z BD → IsPol φ m Z' BD' →
    ∃ θ : Z'.X ≅ Z.X, θ.hom ≫ Z.s = Z'.s ≫ spMap b ∧ Z'.j ≫ θ.hom = Z.j ∧ BD'.idealSheaf = BD.idealSheaf.comap θ.hom := by
  intro hM E _ _ _ H D l Xo c O O' _ _ β β' Z Z' BD BD' φ m b b' hβ hβ' hft hft' htw hb hb' hp hp'
  have hjs : ∀ {P : Type} [CommRing P] {γ : P →+* c.F} (Y : Model Xo c γ),
      Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap γ := by
    intro P _ γ Y
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hsp : ∀ {P P' : Type} [CommRing P] [CommRing P'] (γ : P →+* c.F) (γ' : P' →+* c.F) (a : P →+* P'),
      γ'.comp a = γ → spMap γ' ≫ spMap a = spMap γ := by
    intro P P' _ _ γ γ' a h
    rw [← h, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨n, -⟩ := GlobalTheory.exists_sabMap_of_base_eq Z'.m0.toSABMap (Category.id_comp (pullback.fst _ _)).symm
  obtain ⟨ν, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel Z.m0.toSABMap n
  obtain ⟨n₂, -⟩ := GlobalTheory.exists_sabMap_of_base_eq Z.m0.toSABMap (Category.id_comp (pullback.fst _ _)).symm
  obtain ⟨ν₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel Z'.m0.toSABMap n₂
  have hrs : 𝟙 _ ≫ Z.j ≫ Z.s = Z'.j ≫ Z'.s ≫ spMap b := by
    rw [Category.id_comp, hjs, ← Category.assoc, hjs, Category.assoc, hsp β β' b hb]
  have hrs₂ : 𝟙 _ ≫ Z'.j ≫ Z'.s = Z.j ≫ Z.s ≫ spMap b' := by
    rw [Category.id_comp, hjs, ← Category.assoc, hjs, Category.assoc, hsp β' β b' hb']
  obtain ⟨π, hπ, -, -, hj, -, hBD⟩ := hM E H D l l Xo Xo c c O O' β β' Z Z' BD BD' φ m b (RingEquiv.refl _) (𝟙 _)
    ((TwMap.reflEquiv _ _ _).symm ν) hβ hβ' hft' htw rfl hp hp' hrs
  obtain ⟨π', -, -, -, hj', -, -⟩ := hM E H D l l Xo Xo c c O' O β' β Z' Z BD' BD φ m b' (RingEquiv.refl _) (𝟙 _)
    ((TwMap.reflEquiv _ _ _).symm ν₂) hβ' hβ hft htw rfl hp' hp hrs₂
  rw [Category.id_comp] at hj hj'
  have h₁ : π ≫ π' = 𝟙 _ := GlobalTheory.ModelRelCompare.hom_ext_j Z' hβ' (by rw [← Category.assoc, hj, hj', Category.comp_id])
  have h₂ : π' ≫ π = 𝟙 _ := GlobalTheory.ModelRelCompare.hom_ext_j Z hβ (by rw [← Category.assoc, hj', hj, Category.comp_id])
  exact ⟨⟨π, π', h₁, h₂⟩, hπ, hj, hBD⟩

end GlobalTheory.PolModelIso
