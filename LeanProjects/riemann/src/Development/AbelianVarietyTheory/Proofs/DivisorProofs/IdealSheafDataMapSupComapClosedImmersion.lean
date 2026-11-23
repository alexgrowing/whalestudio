import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.ClosedImmIdeal

theorem ideal_comap_preimage {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i]
    (J : W.IdealSheafData) (U : W.affineOpens) :
    (J.comap i).ideal ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ = Ideal.map (i.app U.1).hom (J.ideal U) := by
  rw [GlobalTheory.Principalise.comapIdealAffine J i U ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ le_rfl,
    Scheme.Hom.app_eq_appLE]

theorem iSup_preimage_affineOpens {T W : Scheme.{0}} (i : T ⟶ W) :
    ⨆ U : W.affineOpens, i ⁻¹ᵁ U.1 = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

theorem comap_map_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (a : T.IdealSheafData) :
    (a.map i).comap i = a := by
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : W.affineOpens => ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩) (iSup_preimage_affineOpens i) fun U => ?_
  rw [ideal_comap_preimage, Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Ideal.map_comap_of_surjective _ (i.app_surjective U.1 U.2)]

theorem map_comap_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (b : W.IdealSheafData)
    (hb : (⊥ : T.IdealSheafData).map i ≤ b) : (b.comap i).map i = b := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap _ _)
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : W.affineOpens => U)
    (iSup_affineOpens_eq_top W) fun U => ?_
  have h0 := hb U
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at h0 ⊢
  rw [ideal_comap_preimage, Ideal.comap_map_of_surjective _ (i.app_surjective U.1 U.2)]
  refine sup_le le_rfl (le_trans ?_ h0)
  simp

theorem map_sup_comap_and_comap_map : ∀ (T W : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
    ∀ (a : T.IdealSheafData) (J : W.IdealSheafData),
      (a ⊔ J.comap i).map i = a.map i ⊔ J ∧ (a.map i).comap i = a := by
  intro T W i hi a J
  haveI := hi
  refine ⟨?_, comap_map_eq i a⟩
  have hb : (⊥ : T.IdealSheafData).map i ≤ a.map i ⊔ J :=
    le_sup_of_le_left (Scheme.IdealSheafData.map_mono i bot_le)
  rw [← map_comap_eq i _ hb, Scheme.IdealSheafData.comap_sup, comap_map_eq]

end GlobalTheory.ClosedImmIdeal
