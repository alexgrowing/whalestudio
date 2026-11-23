import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingIndex
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

section Local

set_option maxHeartbeats 2000000 in

theorem subsingleton_cohomology_gsFinFamily_of_three_le {n : ℕ} (hn : n ≠ 0)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hM : ∀ m : M, n • m = 0) (v : S) {j : ℕ} (hj : 3 ≤ j) :
    Subsingleton (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom M) j) := by
  refine subsingleton_cohomology_of_cdp_le_two hn (fun ℓ hℓ _ => ?_)
    (Rep.res (gsFinFamily S ιs v).toMonoidHom M) (fun m => hM m) hj
  refine cdp_galois_le_two _ _ hℓ ?_
  exact_mod_cast hℓ.ne_zero

set_option maxHeartbeats 2000000 in

theorem subsingleton_cohomology_real_of_odd (v : {v : InfinitePlace K.1 // v.IsReal}) {n : ℕ}
    (hn : Odd n) (A : Rep.{0} (ULift.{0} ℤ) Gal(AlgebraicClosure v.1.Completion / v.1.Completion))
    [IsDiscreteRep A] (hA : ∀ a : A, n • a = 0) {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (cohomology A j) := by
  suffices h : ∀ z : cohomology A j, z = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro z
  obtain ⟨U, hU⟩ := exists_card_smul_eq_zero A (by omega) z
  have hdvd : Nat.card (Gal(AlgebraicClosure v.1.Completion / v.1.Completion) ⧸ (U : Subgroup _)) ∣ 2 := by
    rw [← card_realGal_eq_two v.1 v.2, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_quotient_dvd_card _
  have h2 : 2 • z = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, mul_comm, mul_smul, hU, smul_zero]
  have hnz : n • z = 0 := nsmul_cohomology_eq_zero A hA j z
  obtain ⟨c, rfl⟩ := hn
  rw [add_smul, mul_comm, mul_smul, h2, smul_zero, zero_add, one_smul] at hnz
  exact hnz

end Local

section Criterion

theorem eq_zero_gsTateCompactCohomology_of_gsRealRes {n : ℕ} (hn : n ≠ 0)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 2 ≤ r)
    (hs : Function.Surjective (gsRealRes S ιr M (r + 1)).hom)
    (hi : Function.Injective (gsRealRes S ιr M (r + 2)).hom)
    (x : gsTateCompactCohomology S ιr ιs M (r + 2)) : x = 0 :=
  tateCompactCohomology_eq_zero_of_surjective_of_injective (gsFinFamily S ιs) (gsRealFamily S ιr) M _
    (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) r
    ((surjective_tateGlobalToLocal_iff _ _ _ _ _ _ _ _ fun v =>
      subsingleton_cohomology_gsFinFamily_of_three_le S ιs hn M hM v (by omega)).2 hs)
    ((injective_tateGlobalToLocal_iff _ _ _ _ _ _ _ _ fun v =>
      subsingleton_cohomology_gsFinFamily_of_three_le S ιs hn M hM v (by omega)).2 hi) x

theorem eq_zero_gsTateCompactCohomology_of_subsingleton
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Subsingleton M]
    {r : ℕ} (hr : 4 ≤ r) (x : gsTateCompactCohomology S ιr ιs M r) : x = 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 2 := ⟨r - 2, by omega⟩
  refine eq_zero_gsTateCompactCohomology_of_gsRealRes S ιs ιr one_ne_zero M
    (fun m => Subsingleton.elim _ _) (by omega) (fun z => ⟨0, funext fun v => ?_⟩) ?_ x
  · have := subsingleton_cohomology_of_subsingleton (Rep.res (gsRealFamily S ιr v).toMonoidHom M) (p + 1)
    exact Subsingleton.elim _ _
  · have := subsingleton_cohomology_of_subsingleton M (p + 2)
    exact fun a b _ => Subsingleton.elim a b

end Criterion

section Odd

theorem eq_zero_gsTateCompactCohomology_of_odd {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hM : ∀ m : M, ℓ • m = 0) {r : ℕ} (hr : 4 ≤ r) (x : gsTateCompactCohomology S ιr ιs M r) :
    x = 0 := by
  have hodd : Odd ℓ := hℓ.odd_of_ne_two h2
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 2 := ⟨r - 2, by omega⟩
  refine eq_zero_gsTateCompactCohomology_of_gsRealRes S ιs ιr hℓ.ne_zero M hM (by omega)
    (fun z => ⟨0, funext fun v => ?_⟩) ?_ x
  · have := subsingleton_cohomology_real_of_odd v hodd (Rep.res (gsRealFamily S ιr v).toMonoidHom M)
      (fun m => hM m) (j := p + 1) (by omega)
    exact Subsingleton.elim _ _
  · have : Subsingleton (cohomology M (p + 2)) :=
      subsingleton_cohomology_of_cdp_le_two hℓ.ne_zero
        (fun q hq hqℓ => cdp_galUnramifiedOutside_le_two_of_dvd K S hℓ.ne_zero hS (Or.inl hodd) hq hqℓ)
        M hM (by omega)
    exact fun a b _ => Subsingleton.elim a b

end Odd

section Devissage

theorem mem_of_natCast_mem_of_dvd {n d : ℕ} (hd : d ∣ n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : ((d : ℕ) : 𝓞 K.1) ∈ v.asIdeal) : v ∈ S := by
  refine hS v ?_
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

theorem eq_zero_gsTateCompactCohomology_of_coind
    (hC : (∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) →
      ∀ (W : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) {r : ℕ}, 4 ≤ r →
        ∀ x : gsTateCompactCohomology S ιr ιs (Rep.coind (W : Subgroup _).subtype
          (zmodRep.{0} (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) 2)) r, x = 0)
    {r : ℕ} (hr : 4 ≤ r) :
    ∀ (n : ℕ), n ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) →
      ∀ (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M],
        (∀ m : M, n • m = 0) → ∀ x : gsTateCompactCohomology S ιr ιs M r, x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hS M _ _ hM x
  by_cases hsub : Subsingleton M
  · exact eq_zero_gsTateCompactCohomology_of_subsingleton S ιs ιr M hr x
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hsub ⟨fun a b => by rw [← one_nsmul a, ← one_nsmul b, hM a, hM b]⟩
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨c, hc⟩ := hℓn
  let T : Submodule (ULift.{0} ℤ) M := LinearMap.ker (ℓ • LinearMap.id)
  have hmemT : ∀ m : M, m ∈ T ↔ ℓ • m = 0 := fun m => Iff.rfl
  have hT : ∀ g, T ≤ T.comap (M.ρ g) := fun g m hm => by
    change ℓ • M.ρ g m = 0
    rw [← map_nsmul, (hmemT m).1 hm, map_zero]
  have hSE := subQuotShortComplex_shortExact M T hT
  have : Finite (subQuotShortComplex M T hT).X₁ := Subtype.finite
  have : Finite (subQuotShortComplex M T hT).X₃ := Finite.of_surjective _ (Submodule.mkQ_surjective T)
  refine eq_zero_tateCompactCohomologyRes_of_shortExact (gsFinFamily S ιs) (gsRealFamily S ιr) hSE r
    ?_ ?_ x
  ·
    have hM₁ : ∀ m : M.subrepresentation T hT, ℓ • m = 0 := fun m => Subtype.ext ((hmemT m.1).1 m.2)
    by_cases h2 : ℓ = 2
    · subst h2
      exact eq_zero_tateCompactCohomologyRes_of_two_nsmul (gsFinFamily S ιs) (gsRealFamily S ιr) r
        (fun W => hC (mem_of_natCast_mem_of_dvd S ⟨c, hc⟩ hS) W hr) _ hM₁
    · exact eq_zero_gsTateCompactCohomology_of_odd S ιs ιr hℓ h2
        (mem_of_natCast_mem_of_dvd S ⟨c, hc⟩ hS) _ hM₁ hr
  ·
    have hc0 : c ≠ 0 := by rintro rfl; exact hn (by rw [hc, mul_zero])
    have hclt : c < n := by
      rw [hc]
      exact lt_mul_left (Nat.pos_of_ne_zero hc0) hℓ.one_lt
    refine ih c hclt hc0 (mem_of_natCast_mem_of_dvd S ⟨ℓ, by rw [hc, mul_comm]⟩ hS) _ ?_
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
    refine (map_nsmul T.mkQ c a).symm.trans ((Submodule.Quotient.mk_eq_zero T).2 ?_)
    rw [hmemT, ← mul_smul, ← hc]
    exact hM a

end Devissage

end

end GroundTheory.ProfCoh
