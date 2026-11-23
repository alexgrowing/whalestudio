import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DimensionKummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DimensionSylow
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SurjectiveOfInjectiveOfInjective
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem subsingleton_cohomology_of_cdp_le_two {n : ℕ} (hn : n ≠ 0)
    (hcd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → cdp ℓ G ≤ 2) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology M r) := by
  have htors : IsAddTorsion M := fun m =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn, hM m⟩
  suffices h : ∀ x : cohomology M r, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  refine eq_zero_of_primaryComponent_eq_bot n hn (fun ℓ hℓ hℓn => ?_) x
    (nsmul_cohomology_eq_zero M hM r x)
  refine primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) M htors ?_
  calc cdp ℓ G ≤ 2 := hcd ℓ hℓ hℓn
    _ < r := by exact_mod_cast (show 2 < r by omega)

end Abstract

section Global

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

instance isDiscreteRep_galRootsOfUnity_gs (m : ℕ) :
    IsDiscreteRep (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) m) :=
  isDiscreteRep_galRootsOfUnity m

instance isDiscreteRep_res_galRootsOfUnity_gs (m : ℕ) (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) :
    IsDiscreteRep (Rep.res U.subtype (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) m)) :=
  isDiscreteRep_res_subtype _ U

theorem nonempty_zmod_addEquiv_rootsOfUnity_gs {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    Nonempty (ZMod ℓ ≃+ Additive (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S))) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ ℓ
  have hmem : ζ ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_pow_eq_one S hℓ.ne_zero (fun v hv h => hv (hS v h)) hζ.pow_eq_one
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ℓ :=
    IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) hζ
      (maxUnramifiedOutside K.1 ℚ̄ S).val.toRingHom.injective
  have hcard := hζ'.card_rootsOfUnity
  have : Finite (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  have : Nontrivial (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hℓ.one_lt)
  obtain ⟨η, hη⟩ := exists_ne (1 : rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S))
  have hη0 : Additive.ofMul η ≠ 0 := hη
  have hηp : ℓ • Additive.ofMul η = 0 := by
    have h := pow_card_eq_one' (G := rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S)) (x := η)
    rw [hcard] at h
    rw [← ofMul_pow, h]
    rfl
  exact ⟨AddEquiv.ofBijective _ ((zmod_lift_zmultiplesHom_injective hη0 hηp).bijective_of_nat_card_le
    (by rw [Nat.card_zmod, Nat.card_congr Additive.ofMul.symm, hcard]))⟩

variable {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem subsingleton_h3_rootsOfUnity (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1) :
    Subsingleton (cohomology (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 3) :=
  ⟨fun x y => (eq_zero_h3_rootsOfUnity_of_h3_sUnits K S ℓ hℓ hS hK
    (fun z hz => eq_zero_of_h3_sUnits K S ℓ hℓ hS z 1 (by rwa [pow_one])) x).trans
    (eq_zero_h3_rootsOfUnity_of_h3_sUnits K S ℓ hℓ hS hK
      (fun z hz => eq_zero_of_h3_sUnits K S ℓ hℓ hS z 1 (by rwa [pow_one])) y).symm⟩

include hℓ hS in

theorem subsingleton_h3_res_rootsOfUnity (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) :
    Subsingleton (cohomology (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 3) := by
  obtain ⟨L, hKL, hL, rfl⟩ := exists_gsOpenSubgroup_eq K S U
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ placesOver S :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  have hKL' : ℓ ≠ 2 ∨ IsTotallyComplex L.1 :=
    hK.imp id fun h => by
      have := h
      exact isTotallyComplex_of_algebra K.1 L.1
  have := subsingleton_h3_rootsOfUnity L (placesOver S) hℓ hSL hKL'
  exact ((gsRootsOfUnityCohomologyIso S hL ℓ 3).toLinearEquiv.toEquiv.symm).subsingleton

include hℓ hS in

theorem cdp_galUnramifiedOutside_le_two (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1) :
    cdp ℓ (galUnramifiedOutside K.1 ℚ̄ S) ≤ 2 := by
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity_gs K S hℓ hS
  exact cdp_le_of_forall_openSubgroup hℓ (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) e 2
    (subsingleton_h3_res_rootsOfUnity K S hℓ hS hK)

end Global

section Vanishing

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) {n : ℕ} (hn : n ≠ 0)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ IsTotallyComplex K.1)

include hn hS hK in

theorem cdp_galUnramifiedOutside_le_two_of_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ℓ ∣ n) :
    cdp ℓ (galUnramifiedOutside K.1 ℚ̄ S) ≤ 2 := by
  refine cdp_galUnramifiedOutside_le_two K S hℓ (fun v hv => hS v ?_) ?_
  · obtain ⟨c, hc⟩ := hℓn
    rw [hc, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hv
  · refine hK.imp (fun ho h2 => ?_) id
    rw [h2] at hℓn
    exact (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 hℓn)

include hn hS hK in

theorem subsingleton_cohomology_gs_of_three_le (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (M : Rep.{0} (ULift.{0} ℤ) (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) [IsDiscreteRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology M r) :=
  subsingleton_cohomology_of_cdp_le_two hn (fun ℓ hℓ hℓn =>
    (cdp_openSubgroup_le ℓ U).trans (cdp_galUnramifiedOutside_le_two_of_dvd K S hn hS hK hℓ hℓn)) M hM hr

include hn hS hK in

theorem subsingleton_h3_res_rootsOfUnity_of_odd (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) :
    Subsingleton (cohomology (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n)) 3) :=
  subsingleton_cohomology_gs_of_three_le K S hn hS hK U _
    (fun m => nsmul_rootsOfUnity_eq_zero (E := maxUnramifiedOutside K.1 ℚ̄ S) n m) le_rfl

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

set_option maxHeartbeats 2000000 in
include hn hS hK in

theorem subsingleton_compactCohomology_four (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] (hM : ∀ m : M, n • m = 0) :
    Subsingleton (compactCohomologyRes (gsFinFamily S ιs) M 4) := by
  suffices h : ∀ x : compactCohomologyRes (gsFinFamily S ιs) M 4, x = 0 from
    ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  have hglob : Subsingleton (cohomology M 4) :=
    subsingleton_cohomology_of_cdp_le_two hn
      (fun ℓ hℓ hℓn => cdp_galUnramifiedOutside_le_two_of_dvd K S hn hS hK hℓ hℓn) M hM (by norm_num)
  have hloc : ∀ v : S, Subsingleton (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom M) 3) := by
    intro v
    refine subsingleton_cohomology_of_cdp_le_two hn (fun ℓ hℓ _ => ?_)
      (Rep.res (gsFinFamily S ιs v).toMonoidHom M) (fun m => hM m) le_rfl
    refine cdp_galois_le_two _ _ hℓ ?_
    exact_mod_cast hℓ.ne_zero
  obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (compactCohomology_exact_compact (gsFinFamily S ιs) M _ (fun _ => 𝟙 _) 3) x
    (Subsingleton.elim _ _)
  have : Subsingleton (∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom M) 3) :=
    Pi.instSubsingleton
  rw [Subsingleton.elim y 0, map_zero]

end Vanishing

end

end GroundTheory.ProfCoh
