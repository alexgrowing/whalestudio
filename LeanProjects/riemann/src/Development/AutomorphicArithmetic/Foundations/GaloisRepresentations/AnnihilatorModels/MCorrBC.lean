import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem etale_restrict_of_isPullback {X Y W Z : Scheme.{0}} {h : Y ⟶ X} {t : W ⟶ X} {s : Z ⟶ Y} {g : Z ⟶ W}
    (hpb : IsPullback s g h t) (U : X.Opens) (ht : Etale (t ∣_ U)) : Etale (s ∣_ (h ⁻¹ᵁ U)) := by
  have P1 := isPullback_morphismRestrict t U
  have P2 := isPullback_morphismRestrict s (h ⁻¹ᵁ U)
  have P3 := isPullback_morphismRestrict h U
  have hcomm : ((s ∣_ (h ⁻¹ᵁ U)) ≫ (h ∣_ U)) ≫ U.ι = (s ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g ≫ t := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, Category.assoc, hpb.w]
  let top : (s ⁻¹ᵁ (h ⁻¹ᵁ U)).toScheme ⟶ (t ⁻¹ᵁ U).toScheme :=
    P1.lift ((s ∣_ (h ⁻¹ᵁ U)) ≫ (h ∣_ U)) ((s ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g) (by rw [hcomm, Category.assoc])
  have htop₁ : top ≫ (t ∣_ U) = (s ∣_ (h ⁻¹ᵁ U)) ≫ (h ∣_ U) := P1.lift_fst _ _ _
  have htop₂ : top ≫ (t ⁻¹ᵁ U).ι = (s ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g := P1.lift_snd _ _ _
  have pasted := P2.flip.paste_horiz hpb.flip
  have pasted' : IsPullback (top ≫ (t ⁻¹ᵁ U).ι) (s ∣_ (h ⁻¹ᵁ U)) t ((h ∣_ U) ≫ U.ι) := by
    rw [htop₂, morphismRestrict_ι]; exact pasted
  have left : IsPullback top (s ∣_ (h ⁻¹ᵁ U)) (t ∣_ U) (h ∣_ U) :=
    IsPullback.of_right pasted' htop₁ P1.flip
  exact MorphismProperty.of_isPullback (P := @Etale) left ht

theorem UpperTheory.Gal.crystallineComparison.Mod.corrBC_of :
    WModEx → RankN → SecEquiv → GrCard → CorrBC := by
  intro hW hR hS hG p _ D O _ _ _ _ f b N r w _ hstd M j hj T Y Z h s g hpb
  refine ⟨?_, ?_, ?_⟩
  · have := T.fin
    exact MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip this
  · have hV : Y.basicOpen ((p : ℕ) : Γ(Y, ⊤)) = h ⁻¹ᵁ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) := by
      rw [Scheme.preimage_basicOpen_top, map_natCast]
    rw [hV]
    exact etale_restrict_of_isPullback hpb _ T.et
  · intro K _ _ hp y
    haveI : ValuationRing K := ValuationRing.of_field K
    haveI : IsAlgClosed (FractionRing K) :=
      IsAlgClosed.of_ringEquiv K (FractionRing K) (FractionRing.algEquiv K K).symm.toRingEquiv
    obtain ⟨W⟩ := hW p D O b N M.X M.s M.univ w (Over.mk (y ≫ h))
    obtain ⟨hfin, hrk⟩ := hR p D O f b N r w hstd M K hp (y ≫ h) W
    obtain ⟨e, -⟩ := hS p D O f b N r w hstd M j hj T K hp (y ≫ h) W
    let E : {z : Spec (CommRingCat.of K) ⟶ Z // z ≫ s = y} ≃ {z : Sp K ⟶ T.Y // z ≫ T.s = y ≫ h} :=
      { toFun := fun z => ⟨z.1 ≫ g, by rw [Category.assoc, ← hpb.w, ← Category.assoc, z.2]⟩
        invFun := fun z => ⟨hpb.lift y z.1 z.2.symm, hpb.lift_fst _ _ _⟩
        left_inv := fun z => Subtype.ext (hpb.hom_ext (by rw [hpb.lift_fst, z.2]) (by rw [hpb.lift_snd]))
        right_inv := fun z => Subtype.ext (hpb.lift_snd _ _ _) }
    rw [Nat.card_congr E, Nat.card_congr e]
    exact hG _ _ _ _ hrk
