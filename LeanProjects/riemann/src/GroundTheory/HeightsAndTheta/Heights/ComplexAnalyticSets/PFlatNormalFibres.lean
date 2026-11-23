import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreCriterion
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreRFlatAscent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreSFlatAscent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem SerreRAt.of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {k : ℕ}
    (h : SerreRAt A k) : SerreRAt B k := fun hd => by
  have := h (by rwa [ringKrullDim_eq_of_ringEquiv e])
  exact IsRegularLocalRing.of_ringEquiv e

theorem SerreSAt.of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) {k : ℕ} (h : SerreSAt A k) : SerreSAt B k := by
  obtain ⟨rs, hmem, hreg, hlen⟩ := h
  refine ⟨rs.map e, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    have := hmem s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun hu => this ((isUnit_map_iff e s).mp hu)
  · refine (AddEquiv.isWeaklyRegular_congr (e := e.toAddEquiv) ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => by
      simp [smul_eq_mul])
  · rwa [List.length_map, ← ringKrullDim_eq_of_ringEquiv e]

noncomputable def localizationAtMaximalEquiv (B : Type*) [CommRing B] [IsLocalRing B] :
    Localization.AtPrime (maximalIdeal B) ≃+* B :=
  (IsLocalization.atUnits B (maximalIdeal B).primeCompl (fun x hx => by
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsUnit.mem_submonoid_iff] using hx)).toRingEquiv.symm

theorem normalRing_of_isIntegrallyClosed (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] :
    NormalRing B := fun P _ =>
  ⟨inferInstance, isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl
    P.primeCompl_le_nonZeroDivisors⟩

theorem serreAt_of_isIntegrallyClosed (hC : SerreCriterion.Statement) (B : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] : SerreRAt B 1 ∧ SerreSAt B 2 := by
  obtain ⟨h1, h2⟩ := (hC B inferInstance).mp (normalRing_of_isIntegrallyClosed B)
  exact ⟨(h1 (maximalIdeal B)).of_ringEquiv (localizationAtMaximalEquiv B),
    (h2 (maximalIdeal B)).of_ringEquiv (localizationAtMaximalEquiv B)⟩

theorem FlatNormalFibres.proof (hC : SerreCriterion.Statement) (hR : SerreRFlatAscent.Statement)
    (hS : SerreSFlatAscent.Statement) : FlatNormalFibres.Statement := by
  intro R S _ _ _ hRn hSn hloc hflat hdom hic hfib
  obtain ⟨hR1, hR2⟩ := (hC R hRn).mp (normalRing_of_isIntegrallyClosed R)
  have hfib' : ∀ (P : Ideal S) [P.IsPrime],
      SerreRAt (primeFibreLocalRing R P) 1 ∧ SerreSAt (primeFibreLocalRing R P) 2 := fun P _ => by
    obtain ⟨h1, h2⟩ := hfib P
    exact serreAt_of_isIntegrallyClosed hC _
  have hN : NormalRing S := (hC S hSn).mpr
    ⟨hR R S hRn hSn hflat 1 hR1 fun P _ => (hfib' P).1, hS R S hRn hSn hflat 2 hR2 fun P _ => (hfib' P).2⟩
  obtain ⟨hd, hi⟩ := hN (maximalIdeal S)
  exact ⟨(localizationAtMaximalEquiv S).symm.toMulEquiv.isDomain,
    IsIntegrallyClosed.of_equiv (localizationAtMaximalEquiv S)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
