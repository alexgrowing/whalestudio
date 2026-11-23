import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem baseIdeal_comp_eq_comap (R : Type) [CommRing R] (J : Ideal R) {W T : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) :
    baseIdeal (i ≫ f) J = (baseIdeal f J).comap i := by
  set m := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  obtain ⟨h0c, h0k, -⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J W _ f (pullback.fst f m) (pullback.snd f m)
    (IsPullback.of_hasPullback f m)
  obtain ⟨-, h1k, -⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J T _ (i ≫ f) (pullback.fst (i ≫ f) m) (pullback.snd (i ≫ f) m)
    (IsPullback.of_hasPullback (i ≫ f) m)
  haveI := h0c
  rw [← h1k, ← h0k, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← pullbackRightPullbackFstIso_hom_fst f m i, Scheme.Hom.ker_comp_of_isIso]

theorem map_baseIdeal_comp (R : Type) [CommRing R] (J : Ideal R) {W T : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) (hi : IsClosedImmersion i) :
    (baseIdeal (i ≫ f) J).map i = i.ker ⊔ baseIdeal f J := by
  have h := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion T W i hi ⊥ (baseIdeal f J)).1
  rw [bot_sup_eq, Scheme.IdealSheafData.map_bot] at h
  rw [baseIdeal_comp_eq_comap, h]

theorem reduces_iff_ker_eq : ∀ (R : Type) [CommRing R] (J : Ideal R) (W T Y : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) (j : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))), IsClosedImmersion i → IsClosedImmersion j → j ≫ f = q ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ((∃ b : Y ⟶ T, b ≫ i = j ∧ IsPullback b q (i ≫ f) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ↔ i.ker ⊔ baseIdeal f J = j.ker) := by
  intro R _ J W T Y f i j q hi hj hq
  haveI := hi
  haveI := hj
  constructor
  · rintro ⟨b, hb, hpb⟩
    obtain ⟨-, hbk, -⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J T Y (i ≫ f) b q hpb
    rw [← hb, Scheme.Hom.ker_comp, hbk, map_baseIdeal_comp R J f i hi]
  · intro hk
    set m := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    obtain ⟨h1c, h1k, -⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J T _ (i ≫ f) (pullback.fst (i ≫ f) m)
      (pullback.snd (i ≫ f) m) (IsPullback.of_hasPullback (i ≫ f) m)
    haveI := h1c
    have hker : (pullback.fst (i ≫ f) m ≫ i).ker = j.ker := by
      rw [Scheme.Hom.ker_comp, h1k, map_baseIdeal_comp R J f i hi, hk]
    let e := IsClosedImmersion.lift (pullback.fst (i ≫ f) m ≫ i) j hker.le
    have he : e ≫ pullback.fst (i ≫ f) m ≫ i = j := IsClosedImmersion.lift_fac _ _ _
    haveI : IsIso e := IsClosedImmersion.isIso_of_ker_eq j _ e he hker.symm
    haveI : IsClosedImmersion m := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono m := inferInstance
    have hqe : e ≫ pullback.snd (i ≫ f) m = q := by
      rw [← cancel_mono m, ← hq, Category.assoc, ← pullback.condition, ← he]
      simp only [Category.assoc]
    refine ⟨e ≫ pullback.fst (i ≫ f) m, by rw [Category.assoc, he], ?_⟩
    rw [← hqe]
    exact IsPullback.of_iso (IsPullback.of_hasPullback (i ≫ f) m) (asIso e).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

end GlobalTheory.FormalAlg
