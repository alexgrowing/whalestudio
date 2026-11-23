import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FlatBaseChangeIdeal

theorem toImage_std {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_
  · have := f.imageι.preimage_iSup (fun U : Y.affineOpens ↦ U.1)
    rw [← this, iSup_affineOpens_eq_top]
    simp
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

theorem ker_comap_flat {X Y V : Scheme.{0}} (h : X ⟶ Y) [QuasiCompact h] (g : V ⟶ Y) [Flat g] :
    h.ker.comap g = (pullback.fst g h).ker := by
  have := toImage_std h
  let m : pullback g h ⟶ pullback g h.imageι :=
    pullback.map g h g h.imageι (𝟙 _) h.toImage (𝟙 _) (by simp) (by simp)
  have hm1 : m ≫ pullback.fst g h.imageι = pullback.fst g h := by
    simp only [m, pullback.lift_fst, Category.comp_id]
  have hm2 : m ≫ pullback.snd g h.imageι = pullback.snd g h ≫ h.toImage := by
    simp only [m, pullback.lift_snd]
  have big : IsPullback (pullback.snd g h) (m ≫ pullback.fst g h.imageι)
      (h.toImage ≫ h.imageι) g := by
    rw [hm1, h.toImage_imageι]; exact (IsPullback.of_hasPullback g h).flip
  have hsq : IsPullback (pullback.snd g h) m h.toImage (pullback.snd g h.imageι) :=
    IsPullback.of_bot big hm2.symm (IsPullback.of_hasPullback g h.imageι).flip
  have hd : IsSchemeTheoreticallyDominant m := IsSchemeTheoreticallyDominant.of_isPullback hsq
  rw [← hm1, Scheme.Hom.ker_comp, hd.ker_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  congr 1
  exact (Scheme.IdealSheafData.ker_subschemeι _).symm

end GlobalTheory.FlatBaseChangeIdeal

namespace GlobalTheory.FlatBaseChangeIdeal

theorem map_comap_flat : ∀ (W W' V V' : Scheme.{0}) (π : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W')
    (π' : V' ⟶ V), IsPullback g' π' π g → Flat g → QuasiCompact π →
    ∀ T : W'.IdealSheafData, (T.map π).comap g = (T.comap g').map π' := by
  intro W W' V V' π g g' π' H hg hπ T
  have big : IsPullback (pullback.snd g' T.subschemeι) (pullback.fst g' T.subschemeι ≫ π')
      (T.subschemeι ≫ π) g :=
    (IsPullback.of_hasPullback g' T.subschemeι).flip.paste_vert H
  rw [Scheme.IdealSheafData.map, ker_comap_flat, Scheme.IdealSheafData.comap,
    Scheme.IdealSheafData.map_ker, ← big.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end GlobalTheory.FlatBaseChangeIdeal
