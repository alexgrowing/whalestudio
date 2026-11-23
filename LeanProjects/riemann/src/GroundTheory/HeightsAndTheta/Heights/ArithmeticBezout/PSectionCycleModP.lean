import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionCycleModP
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

namespace SectionCycleModP

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime)

variable {n : ℕ} {F : Type} [Field F]

def red (n : ℕ) (F : Type) [Field F] : MRing (PBlk n) →+* MvPolynomial (Fin n) F :=
  (MvPolynomial.map (Int.castRingHom F)).comp
    ((renameEquiv ℤ (VerticalPartMultiplicity.eb n)).symm.toRingEquiv :
      MRing (PBlk n) →+* MvPolynomial (Fin n) ℤ)

theorem red_surjective (hF : Function.Surjective (Int.castRingHom F)) :
    Function.Surjective (red n F) :=
  (MvPolynomial.map_surjective _ hF).comp (RingEquiv.surjective _)

theorem red_X (i : Fin n) : red n F (X ⟨(), i⟩) = X i := by
  simp [red, VerticalPartMultiplicity.eb]

theorem finIdeal_map (J : Ideal (MRing (PBlk n))) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal J).map (MvPolynomial.map (Int.castRingHom F)) = J.map (red n F) := by
  rw [VerticalPartMultiplicity.finIdeal_eq_map, Ideal.map_map]
  rfl

theorem ker_red_le {p : ℕ} (hp : p.Prime) (hpF : ((p : ℤ) : F) = 0) {W : Ideal (MRing (PBlk n))}
    (hW : C (p : ℤ) ∈ W) : RingHom.ker (red n F) ≤ W := by
  have : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr (by exact_mod_cast hpF)
  have hk : RingHom.ker (Int.castRingHom F) = Ideal.span {(p : ℤ)} := by
    ext a
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, eq_intCast, CharP.intCast_eq_zero_iff F p]
  intro f hf
  have hf' : (renameEquiv ℤ (VerticalPartMultiplicity.eb n)).symm f ∈
      RingHom.ker (MvPolynomial.map (σ := Fin n) (Int.castRingHom F)) := hf
  rw [MvPolynomial.ker_map, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hf'
  obtain ⟨q, hq⟩ := hf'
  have hfq : f = C (p : ℤ) * rename (VerticalPartMultiplicity.eb n) q := by
    have h1 := congrArg (renameEquiv ℤ (VerticalPartMultiplicity.eb n)) hq
    rw [AlgEquiv.apply_symm_apply] at h1
    rw [h1, map_mul]
    simp
  rw [hfq]
  exact W.mul_mem_right _ hW

theorem comap_map_red (hF : Function.Surjective (Int.castRingHom F)) {I : Ideal (MRing (PBlk n))}
    (hI : RingHom.ker (red n F) ≤ I) : (I.map (red n F)).comap (red n F) = I := by
  rw [Ideal.comap_map_of_surjective _ (red_surjective hF), ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr hI]

theorem isRelevant_map_iff (hF : Function.Surjective (Int.castRingHom F)) {W' : Ideal (MRing (PBlk n))}
    (hk : RingHom.ker (red n F) ≤ W') :
    IsRelevant (W'.map (red n F)) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W' := by
  have hmem : ∀ j : Fin n, (X j : MvPolynomial (Fin n) F) ∈ W'.map (red n F) ↔
      (X ⟨(), j⟩ : MRing (PBlk n)) ∈ W' := by
    intro j
    rw [← red_X, ← Ideal.mem_comap, comap_map_red hF hk]
  simp only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, hmem]
  exact ⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩

theorem localMult_map (hF : Function.Surjective (Int.castRingHom F)) {J W' : Ideal (MRing (PBlk n))}
    [hW' : W'.IsPrime] (hJ : RingHom.ker (red n F) ≤ J) (hJW : J ≤ W') :
    localMult (J.map (red n F)) (W'.map (red n F)) = ReciprocityTheory.ChartRestriction.G.Geo.multAt J W' := by
  have hsurj := red_surjective (n := n) hF
  have hkW : RingHom.ker (red n F) ≤ W' := hJ.trans hJW
  have hQ : (W'.map (red n F)).IsPrime := Ideal.map_isPrime_of_surjective hsurj hkW
  let e : (MRing (PBlk n) ⧸ J) ≃+* (MvPolynomial (Fin n) F ⧸ J.map (red n F)) :=
    (Ideal.quotEquivOfEq (by rw [← RingHom.comap_ker, Ideal.mk_ker, comap_map_red hF hJ])).trans
      (RingHom.quotientKerEquivOfSurjective
        (f := (Ideal.Quotient.mk (J.map (red n F))).comp (red n F))
        (Ideal.Quotient.mk_surjective.comp hsurj))
  have he : ∀ x, e (Ideal.Quotient.mk J x) = Ideal.Quotient.mk _ (red n F x) := fun _ => rfl
  have hlen := NumbersDVR.length_localizedModule_eq_of_surjective (red n F) hsurj (W'.map (red n F)) W'
    (comap_map_red hF hkW).symm _ _ e.toAddEquiv fun s x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      change e (Ideal.Quotient.mk _ (s * y)) = Ideal.Quotient.mk _ (red n F s) * e (Ideal.Quotient.mk _ y)
      rw [he, he, map_mul, map_mul]
  unfold localMult ReciprocityTheory.ChartRestriction.G.Geo.multAt
  rw [dif_pos hQ, dif_pos hW', ← VerticalPartMultiplicity.length_localizedModule_quotient, hlen]

theorem proof : SectionCycleModP.Statement := by
  intro n p W F _ hp _ hpW hF hpF i _
  classical
  have hsurj := red_surjective (n := n) hF
  set s : MRing (PBlk n) := X ⟨(), i⟩ with hs
  set J := W ⊔ Ideal.span {s} with hJdef
  have hkJ : RingHom.ker (red n F) ≤ J := (ker_red_le hp hpF hpW).trans le_sup_left
  have hlin : linForm (Pi.single i (1 : F)) = X i := by
    simp [linForm, Pi.single_apply]
  have hJF : (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)) ⊔
      Ideal.span {linForm (Pi.single i (1 : F))} = J.map (red n F) := by
    rw [finIdeal_map, hlin, hJdef, Ideal.map_sup, Ideal.map_span, Set.image_singleton, hs, red_X]
  have hmin : (J.map (red n F)).minimalPrimes = Ideal.map (red n F) '' J.minimalPrimes := by
    rw [Ideal.minimalPrimes_map_of_surjective hsurj, sup_eq_left.mpr hkJ]
  have hfun : (fun W' => (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W').map (MvPolynomial.map (Int.castRingHom F))) =
      Ideal.map (red n F) := funext finIdeal_map
  have hsupp : ∀ W', W' ∈ (ReciprocityTheory.ChartRestriction.G.Geo.divCycle W s).support →
      W' ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp W s := by
    intro W' hW'
    rw [Finsupp.mem_support_iff] at hW'
    by_contra h
    apply hW'
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, if_neg h]
  have hS : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle W s).support : Set (Ideal (MRing (PBlk n)))) ⊆
      {W' | J ≤ W'} := fun W' h => (hsupp W' h).1.1.2
  have hinj : Set.InjOn (Ideal.map (red n F)) {W' : Ideal (MRing (PBlk n)) | J ≤ W'} :=
    fun a ha b hb hab => by
      rw [← comap_map_red hF (hkJ.trans ha), ← comap_map_red hF (hkJ.trans hb), hab]
  unfold divCycle
  rw [hJF, hfun]
  ext Q
  by_cases hQ : ∃ W' ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp W s, W'.map (red n F) = Q
  · obtain ⟨W', hW', rfl⟩ := hQ
    rw [Finsupp.mapDomain_apply' _ _ hS hinj hW'.1.1.2]
    have hrel : W'.map (red n F) ∈ relComps (J.map (red n F)) :=
      ⟨hmin ▸ ⟨W', hW'.1, rfl⟩, (isRelevant_map_iff hF (hkJ.trans hW'.1.1.2)).mpr hW'.2⟩
    have := hW'.1.1.1
    simp only [fundCycle, Finsupp.onFinset_apply, if_pos hrel, ReciprocityTheory.ChartRestriction.G.Geo.divCycle,
      Finsupp.ofSupportFinite_coe, if_pos hW']
    exact localMult_map hF hkJ hW'.1.1.2
  · have hR : Finsupp.mapDomain (Ideal.map (red n F)) (ReciprocityTheory.ChartRestriction.G.Geo.divCycle W s) Q = 0 := by
      rw [← Finsupp.notMem_support_iff]
      intro h
      obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h)
      exact hQ ⟨W', hsupp W' hW', rfl⟩
    rw [hR, fundCycle, Finsupp.onFinset_apply, if_neg]
    rintro ⟨hQm, hQr⟩
    rw [hmin] at hQm
    obtain ⟨W', hW', rfl⟩ := hQm
    exact hQ ⟨W', ⟨hW', (isRelevant_map_iff hF (hkJ.trans hW'.1.2)).mp hQr⟩, rfl⟩

end SectionCycleModP

end ObjectsChow

end GroundTheory.Heights₂.Heights
