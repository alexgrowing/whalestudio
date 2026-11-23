import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfPullbackDegenerationDataRingAutOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationPullbackToPullDegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackUniformisationCompIdPullbackStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gal_map_maximalIdeal_le {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R'] {ρ : R →+* R'} (σ : Gal ρ) :
    (maximalIdeal R').map (Gal.hom σ) ≤ maximalIdeal R' := by
  refine Ideal.map_le_of_le_comap fun x hx => ?_
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply (mem_nonunits_iff.1 ((mem_maximalIdeal x).1 hx))
  have := hu.map (σ.1.symm : R' ≃+* R')
  simpa [Gal.hom] using this

theorem exists_galMap : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ), ∃ a, GalMap hD U' σ a := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ hG' U' σ
  obtain ⟨hR', hinj, -⟩ := hρ
  have hσi : Function.Injective (Gal.hom σ) := σ.1.injective
  obtain ⟨h, hPO⟩ := GlobalTheory.T.exists_selfPullback_degenerationData_ringAutOver R R' ρ hinj D.toPre D'.toPre hD σ
  obtain ⟨A'', U'', hU''⟩ := GlobalTheory.T.exists_uniformisation_pullback_to_pullDeg R' R' _ _ hR' hR' (Gal.hom σ) hσi (gal_map_maximalIdeal_le σ) D' D' h A' G'
    hG' U'
  obtain ⟨hid, hxe, hem⟩ := GlobalTheory.T.exists_pullDeg_identity_self_admissible R' _ hR' D'
  have hsa : IsSemiAbelian ((Over.pullback (specOf (Gal.hom σ))).obj G') := IsSemiAbelian.pullback _ G' hG'
  obtain ⟨-, bc1, -, -, mbc1, -, hU1, -⟩ :=
    GlobalTheory.T.uniformisation_determined_by_degenerationData_normal R' hR' D' A'' ((Over.pullback (specOf (Gal.hom σ))).obj G') hsa U'' D' A' G' hG' U' hid
  obtain ⟨h', bc, hU, hxe', hem', -, hmon⟩ := GlobalTheory.T.isPullbackUniformisation_comp_id_pullback R' R' _ _ (Gal.hom σ) D' D' D' h hid A' A'' A' G'
    ((Over.pullback (specOf (Gal.hom σ))).obj G') G' (Iso.refl _) bc1 U' U'' U' hU'' hU1
  haveI : IsMonHom bc.hom := hmon (by show IsMonHom (𝟙 _); infer_instance) mbc1
  refine ⟨bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)), ?_, h', bc, rfl, hU, ?_⟩
  · exact ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G' (spMap (Gal.hom σ)))).congr (Category.id_comp _) rfl
  · refine ⟨fun x => by rw [hxe', hxe]; exact hPO.1 x, fun b c hb hc => ?_⟩
    rw [hc, hem', reassoc_of% hem]
    exact hPO.2 b _ hb rfl

end GlobalTheory.Mum
