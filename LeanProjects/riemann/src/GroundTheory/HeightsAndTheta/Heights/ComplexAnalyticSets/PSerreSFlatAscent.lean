import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreSFlatAscent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatDimFormula
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatLocalRegularSequence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem isWeaklyRegular_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) {rs : List R}
    (h : IsWeaklyRegular R rs) : IsWeaklyRegular S (rs.map e) :=
  (AddEquiv.isWeaklyRegular_congr (e := e.toAddEquiv) (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun r _ x => by simp [smul_eq_mul]))).mp h

theorem min_add_le_min_add_min {k a b : WithBot ℕ∞} (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min k (a + b) ≤ min k a + min k b := by
  rcases le_total k a with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min hk hb))
  rcases le_total k b with h' | h'
  · rw [min_eq_left h']
    exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min hk ha))
  rw [min_eq_right h, min_eq_right h']
  exact min_le_right _ _

theorem SerreSFlatAscent.proof (hD : FlatDimFormula.Statement) (hR : FlatLocalRegularSequence.Statement) :
    SerreSFlatAscent.Statement := by
  intro A B _ _ _ hA hB hflat k hSA hfib P _
  set p : Ideal A := P.comap (algebraMap A B) with hp
  have : P.LiesOver p := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver p P
  have hAp : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ hA
  have hBP : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ hB

  have hJ : (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) =
      Ideal.map (algebraMap B (Localization.AtPrime P)) (Ideal.map (algebraMap A B) p) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  let e := Ideal.quotEquivOfEq hJ
  obtain ⟨rs, hrs, hrsreg, hrslen⟩ := hSA p
  obtain ⟨ts, hts, htsreg, htslen⟩ := hfib P
  let g := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.map (algebraMap B (Localization.AtPrime P))
    (Ideal.map (algebraMap A B) p)))
  have hg : ∀ t, Ideal.Quotient.mk _ (g t) = t := Function.surjInv_eq _
  set ys := ts.map g with hys
  have hysmap : ys.map (Ideal.Quotient.mk ((maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)))) = ts.map e.symm := by
    rw [hys, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    rw [Function.comp_apply]
    conv_rhs => rw [← hg t]
    simp [e]
  have hysmem : ∀ y ∈ ys, y ∈ maximalIdeal (Localization.AtPrime P) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    have := hts t ht
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun hu => this (hg t ▸ hu.map _)
  have hreg := hR _ _ hAp hBP inferInstance inferInstance rs ys hrs hrsreg hysmem
    (hysmap ▸ isWeaklyRegular_map_ringEquiv e.symm htsreg)
  have hdim := hD _ _ hAp hBP inferInstance inferInstance
  rw [ringKrullDim_eq_of_ringEquiv e] at hdim
  refine ⟨rs.map (algebraMap _ _) ++ ys, ?_, hreg, ?_⟩
  · intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
      exact map_nonunit _ r (hrs r hr)
    · exact hysmem u hu
  · rw [hdim, List.length_append, List.length_map, hys, List.length_map, Nat.cast_add]
    refine (min_add_le_min_add_min (by simp) ringKrullDim_nonneg_of_nontrivial
      ringKrullDim_nonneg_of_nontrivial).trans ?_
    exact add_le_add hrslen htslen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
