import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPNFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusQuasiInverseScaling
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SameKer

theorem exists_iso_of_sameKer : ∀ (Tb : Scheme.{0}) (G' B A' : Over Tb) [GrpObj G'] [GrpObj B] [GrpObj A'] (π' : G' ⟶ B) (χ₁ : A' ⟶ G') (χ₁' : G' ⟶ A') (k : ℕ), IsAbelianScheme A' → IsUnit (k : Γ(Tb, ⊤)) → IsMonHom π' → IsMonHom χ₁ → IsMonHom χ₁' → Flat π'.left → Surjective π'.left → QuasiCompact π'.left → χ₁ ≫ χ₁' = (𝟙 A') ^ k → (∀ (T : Over Tb) (x : T ⟶ G'), x ≫ χ₁' = 1 ↔ x ≫ π' = 1) → ∃ β : A' ⟶ B, IsIso β ∧ IsMonHom β ∧ χ₁' ≫ β = π' := by
  intro Tb G' B A' _ _ _ π' χ₁ χ₁' k hA hk hπ hχ hχ' fl su qc hcomp hker
  obtain ⟨⟨α, hα, hαeq⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Tb G' B A' π' χ₁' hπ hχ' fl su qc
    (fun T x hx => (hker T x).2 hx)
  have ker : ∀ (T : Over Tb) (x : T ⟶ B), x ≫ α = 1 → x = 1 := by
    intro T x hx
    have pb := (IsPullback.of_hasPullback x π').map (Over.forget Tb)
    have : Flat (pullback.fst x π').left := MorphismProperty.of_isPullback (P := @Flat) pb.flip fl
    have : Surjective (pullback.fst x π').left :=
      MorphismProperty.of_isPullback (P := @Surjective) pb.flip su
    have : Epi (pullback.fst x π').left := Flat.epi_of_flat_of_surjective _
    have : Epi (pullback.fst x π') := Over.epi_of_epi_left _
    have h1 : pullback.snd x π' ≫ χ₁' = 1 := by
      rw [← hαeq, ← Category.assoc, ← pullback.condition, Category.assoc, hx, MonObj.comp_one]
    have h2 := (hker _ _).1 h1
    rw [← cancel_epi (pullback.fst x π'), pullback.condition, h2, MonObj.comp_one]
  have hmono : Mono α := ⟨fun {Z} u v huv => by
    have h : (u * v⁻¹) ≫ α = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
    exact mul_inv_eq_one.1 (ker _ _ h)⟩
  obtain ⟨hkm, hkf, hke, hks⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective Tb A' k hA hk
  obtain ⟨⟨β, hβ, hβeq⟩, hepik⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Tb A' A' B ((𝟙 A') ^ k)
    (χ₁ ≫ π') hkm inferInstance inferInstance hks inferInstance (fun T x hx => by
      have h := (hker T (x ≫ χ₁)).1 (by rw [Category.assoc, hcomp, hx])
      rw [Category.assoc] at h
      exact h)
  have e1 : β ≫ α = 𝟙 A' := by
    rw [← cancel_epi ((𝟙 A') ^ k), ← Category.assoc, hβeq, Category.assoc, hαeq, hcomp, Category.comp_id]
  have e2 : α ≫ β = 𝟙 B := by
    rw [← cancel_mono α, Category.assoc, e1, Category.comp_id, Category.id_comp]
  refine ⟨β, ⟨⟨α, e1, e2⟩⟩, hβ, ?_⟩
  rw [← hαeq, Category.assoc, e2, Category.comp_id]

end GlobalTheory.SameKer
