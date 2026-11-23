import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxSynthPendingDepth 1

attribute [local instance] MvPolynomial.algebraMvPolynomial in

theorem GlobalTheory.CompanionTheory.Ar.Num.divCycle_map_localisation :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (Mo : Submonoid R) [IsLocalization Mo R'] (P : Ideal (MRing ι R)) (f : MRing ι R) (W' : Ideal (MRing ι R')), W'.IsPrime → divCycle (P.map (MvPolynomial.map (algebraMap R R'))) (MvPolynomial.map (algebraMap R R') f) W' = divCycle P f (W'.comap (MvPolynomial.map (algebraMap R R'))) := by
  intro K _ _ ι _ R R' _ _ _ Mo _ P f W' hW'
  classical
  let φ : MRing ι R →+* MRing ι R' := MvPolynomial.map (algebraMap R R')
  let M : Submonoid (MRing ι R) := Mo.map (C (σ := (Σ k, ι k)) (R := R))
  haveI : IsLocalization M (MRing ι R') := MvPolynomial.isLocalization Mo R'
  have hφ : algebraMap (MRing ι R) (MRing ι R') = φ := rfl
  set J := P ⊔ Ideal.span {f} with hJdef
  have hJ : P.map φ ⊔ Ideal.span {φ f} = J.map (algebraMap (MRing ι R) (MRing ι R')) := by
    rw [hφ, hJdef, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hdisj : Disjoint (M : Set (MRing ι R)) (W'.comap (algebraMap (MRing ι R) (MRing ι R'))) :=
    (IsLocalization.isPrime_iff_isPrime_disjoint M (MRing ι R') W').mp hW' |>.2
  have hWp : (W'.comap (algebraMap (MRing ι R) (MRing ι R'))).IsPrime := Ideal.comap_isPrime _ _
  have hmap : (W'.comap (algebraMap (MRing ι R) (MRing ι R'))).map
      (algebraMap (MRing ι R) (MRing ι R')) = W' := IsLocalization.map_comap M _ W'
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = W'.comap (algebraMap (MRing ι R) (MRing ι R')) := ⟨_, rfl⟩
  rw [← hQ] at hdisj hWp hmap
  subst hmap
  have hmin : Q.map (algebraMap (MRing ι R) (MRing ι R')) ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes ↔
      Q ∈ J.minimalPrimes := by
    rw [hJ, IsLocalization.minimalPrimes_map M]
    show (Q.map (algebraMap (MRing ι R) (MRing ι R'))).comap
      (algebraMap (MRing ι R) (MRing ι R')) ∈ J.minimalPrimes ↔ _
    rw [← hQ]
  have hrel : IsRelevant (Q.map (algebraMap (MRing ι R) (MRing ι R'))) ↔ IsRelevant Q := by
    refine forall_congr' fun k => exists_congr fun i => not_congr ?_
    have hX : (X ⟨k, i⟩ : MRing ι R') =
        algebraMap (MRing ι R) (MRing ι R') (X ⟨k, i⟩) := (MvPolynomial.map_X _ _).symm
    rw [hX, ← Ideal.mem_comap, ← hQ]
  have hl : ∀ (h₁ : Q.IsPrime) (h₂ : (Q.map (algebraMap (MRing ι R) (MRing ι R'))).IsPrime),
      @multAt _ _ _ _ J Q h₁ =
        @multAt _ _ _ _ (P.map φ ⊔ Ideal.span {φ f})
          (Q.map (algebraMap (MRing ι R) (MRing ι R'))) h₂ := by
    intro h₁ h₂
    unfold multAt
    rw [hJ]
    exact GenericCycleCorresp.length_eq M J Q hdisj
  have hQ' : Ideal.comap (MvPolynomial.map (algebraMap R R') : MRing ι R →+* MRing ι R')
      (Q.map (algebraMap (MRing ι R) (MRing ι R'))) = Q := hQ.symm
  rw [hQ']
  change divCycle (P.map φ) (φ f) _ = divCycle P f Q
  unfold divCycle
  by_cases hc : Q ∈ J.minimalPrimes ∧ IsRelevant Q
  · rw [dif_pos ⟨hmin.mpr hc.1, hrel.mpr hc.2⟩, dif_pos hc, hl]
  · rw [dif_neg (fun h => hc ⟨hmin.mp h.1, hrel.mp h.2⟩), dif_neg hc]
