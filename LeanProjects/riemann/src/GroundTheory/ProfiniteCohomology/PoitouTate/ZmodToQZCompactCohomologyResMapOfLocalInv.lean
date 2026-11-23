import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.General
import GroundTheory.ProfiniteCohomology.PoitouTate.Primary
import GroundTheory.ProfiniteCohomology.PoitouTate.BrauerInvZOfIsSepClosureCohomologyULiftIntAddEqu
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteCompact
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

theorem natCast_mem_of_natCard_mem {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime)
    {A : Type*} [AddCommGroup A] [Finite A] {n : ℕ} (hA : ∀ a : A, n • a = 0)
    (h : ((Nat.card A : ℕ) : R) ∈ P) : ((n : ℕ) : R) ∈ P := by
  obtain ⟨c, hc⟩ := card_dvd_exponent_nsmul_rank' A hA
  refine hP.mem_of_pow_mem (AddGroup.rank A) ?_
  rw [← Nat.cast_pow, hc, Nat.cast_mul]
  exact P.mul_mem_right _ h

instance neZero_ordProj {N : ℕ} (p : ℕ) : NeZero (p ^ N.factorization p) :=
  ⟨(Nat.ordProj_pos N p).ne'⟩

section Natural

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {A B : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep A] [IsDiscreteRep B]

abbrev resMap (v : ι) (g : A ⟶ B) : Rep.res (φ v).toMonoidHom A ⟶ Rep.res (φ v).toMonoidHom B :=
  (Rep.resFunctor (φ v).toMonoidHom).map g

theorem compactCohomologyResMap_localToCompact (g : A ⟶ B) (n : ℕ)
    (ξ : ∀ v, cohomology (Rep.res (φ v).toMonoidHom A) n) :
    (compactCohomologyResMap φ g (n + 1)).hom
        ((localToCompact φ A _ (fun _ => 𝟙 _) n).hom ξ) =
      (localToCompact φ B _ (fun _ => 𝟙 _) n).hom
        (fun v => (cohomologyMap (resMap φ v g) n).hom (ξ v)) :=
  ConcreteCategory.congr_hom (localToCompact_compactCohomologyMap φ (A := A) (B := B)
    (Aᵥ := fun v => Rep.res (φ v).toMonoidHom A) (Bᵥ := fun v => Rep.res (φ v).toMonoidHom B)
    (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (g := g) (gᵥ := fun v => resMap φ v g)
    (hg := fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) (n := n)) ξ

theorem cohomologyMap_toAddMonoidHom_comp {C : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep C] (f : A ⟶ B)
    (g : B ⟶ C) (n : ℕ) :
    (cohomologyMap g n).hom.toAddMonoidHom.comp (cohomologyMap f n).hom.toAddMonoidHom =
      (cohomologyMap (f ≫ g) n).hom.toAddMonoidHom := by
  rw [cohomologyMap_comp]
  rfl

theorem zmodToQZ_compactCohomologyResMap_of_localInv [Fintype ι] {q n : ℕ}
    (j : A ⟶ B) (tA : compactCohomologyRes φ A 3 →+ ZMod q) (tB : compactCohomologyRes φ B 3 →+ ZMod n)
    (invA : ∀ v, cohomology (Rep.res (φ v).toMonoidHom A) 2 →+ QZ)
    (invB : ∀ v, cohomology (Rep.res (φ v).toMonoidHom B) 2 →+ QZ)
    (hinv : ∀ v, (invB v).comp (cohomologyMap (resMap φ v j) 2).hom.toAddMonoidHom = invA v)
    (htA : ∀ ξ, zmodToQZ q (tA ((localToCompact φ A _ (fun _ => 𝟙 _) 2).hom ξ)) = ∑ v, invA v (ξ v))
    (htB : ∀ ξ, zmodToQZ n (tB ((localToCompact φ B _ (fun _ => 𝟙 _) 2).hom ξ)) = ∑ v, invB v (ξ v))
    (hsurj : Function.Surjective (localToCompact φ A _ (fun _ => 𝟙 _) 2).hom)
    (z : compactCohomologyRes φ A 3) :
    zmodToQZ n (tB ((compactCohomologyResMap φ j 3).hom z)) = zmodToQZ q (tA z) := by
  obtain ⟨ξ, rfl⟩ := hsurj z
  rw [compactCohomologyResMap_localToCompact, htB, htA]
  exact Finset.sum_congr rfl fun v _ => DFunLike.congr_fun (hinv v) (ξ v)

end Natural

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Facts

variable {n : ℕ} [NeZero n] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ IsTotallyComplex K.1)

include hS hK in

theorem subsingleton_cohomology_gs_of_nsmul (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology M r) :=
  subsingleton_cohomology_of_cdp_le_two (NeZero.ne n)
    (fun _ hℓ hℓn => cdp_galUnramifiedOutside_le_two_of_dvd K S (NeZero.ne n) hS hK hℓ hℓn) M hM hr

include hS hK in

theorem finite_cohomology_gs_of_nsmul [Finite S]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) (r : ℕ) : Finite (cohomology M r) := by
  rcases le_or_gt r 2 with hr | hr
  · exact finite_cohomology_gs K S M
      (fun v hv => hS v (natCast_mem_of_natCard_mem v.isPrime hM hv)) r hr
  · have := subsingleton_cohomology_gs_of_nsmul S hS hK M hM (show 3 ≤ r by omega)
    exact Finite.of_subsingleton

include hS hK in

theorem finite_compactCohomologyRes_gs_of_nsmul [Finite S]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) (r : ℕ) : Finite (compactCohomologyRes (gsFinFamily S ιs) M r) := by
  have := finite_cohomology_gs_of_nsmul S hS hK M hM r
  exact finite_compactCohomologyRes_gs_of_finite K S ιs M r

include hS in

theorem nonempty_addEquiv_gsRoots_of_mem : Nonempty (gsRoots S n ≃+ ZMod n) := by
  have hcard : Nat.card (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)) = Nat.card (Multiplicative (ZMod n)) := by
    rw [card_rootsOfUnity_maxUnramifiedOutside K S n (NeZero.ne n) (fun v hv h => hv (hS v h)),
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact ⟨MulEquiv.toAdditive (mulEquivOfCyclicCardEq hcard)⟩

include hS hK in

theorem subsingleton_cohomology_three_gsRoots : Subsingleton (cohomology (gsRoots S n) 3) :=
  subsingleton_cohomology_gs_of_nsmul S hS hK _ (nsmul_gsRoots S n) le_rfl

variable [Fintype S]

set_option maxHeartbeats 1600000 in

theorem zmodToQZ_gsCompactInv_localToCompact (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    zmodToQZ n (gsCompactInv S ιs n hK h3
        ((localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom ξ)) =
      ∑ v, gsLocalInvRootsQZ S ιs n v (ξ v) := by
  calc _ = zmodToQZ n (gsSumInvRoots S ιs n ξ) := congrArg _ (gsCompactInv_localToCompact S ιs n hK h3 ξ)
    _ = zmodToQZ n (∑ v, gsLocalInvRoots S ιs n v (ξ v)) := congrArg _ (gsSumInvRoots_apply S ιs n ξ)
    _ = ∑ v, zmodToQZ n (gsLocalInvRoots S ιs n v (ξ v)) := map_sum _ _ _
    _ = ∑ v, gsLocalInvRootsQZ S ιs n v (ξ v) :=
      Finset.sum_congr rfl fun v _ => zmodToQZ_gsLocalInvRoots S ιs n v (ξ v)

end Facts

section Level

variable {q n : ℕ}

def gsRootsIncl (hqn : q ∣ n) : gsRoots S q ⟶ gsRoots S n :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive (rootsOfUnity q (maxUnramifiedOutside K.1 ℚ̄ S)))
      (B := Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)))
      (MonoidHom.toAdditive (Subgroup.inclusion (rootsOfUnity_le_of_dvd hqn))),
    fun _ => LinearMap.ext fun _ => rfl⟩

theorem gsRootsIncl_injective (hqn : q ∣ n) : Function.Injective (gsRootsIncl S hqn).hom :=
  fun _ _ hab => Additive.toMul.injective
    (Subgroup.inclusion_injective (rootsOfUnity_le_of_dvd hqn) (congrArg Additive.toMul hab))

theorem gsLocalInvRootsQZ_comp_gsRootsIncl (hqn : q ∣ n) (v : S) :
    (gsLocalInvRootsQZ S ιs n v).comp
        (cohomologyMap (resMap (gsFinFamily S ιs) v (gsRootsIncl S hqn)) 2).hom.toAddMonoidHom =
      gsLocalInvRootsQZ S ιs q v := by
  have hρ : resMap (gsFinFamily S ιs) v (gsRootsIncl S hqn) ≫ gsRootsToLocalUnits S ιs n v =
      gsRootsToLocalUnits S ιs q v :=
    Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  exact ((congrArg (fun F => F.comp
      (cohomologyMap (resMap (gsFinFamily S ιs) v (gsRootsIncl S hqn)) 2).hom.toAddMonoidHom)
      (gsLocalInvRootsQZ_eq_comp S ιs n v)).trans ((AddMonoidHom.comp_assoc _ _ _).trans
      (congrArg (AddMonoidHom.comp _) ((cohomologyMap_toAddMonoidHom_comp _ _ 2).trans
        (congrArg (fun f => (cohomologyMap f 2).hom.toAddMonoidHom) hρ))))).trans
    (gsLocalInvRootsQZ_eq_comp S ιs q v).symm

variable [NeZero q] [NeZero n] [Fintype S]

theorem zmodToQZ_gsCompactInv_gsRootsIncl (hqn : q ∣ n) (hKn : Odd n ∨ IsTotallyComplex K.1)
    (hKq : Odd q ∨ IsTotallyComplex K.1) (h3n : Subsingleton (cohomology (gsRoots S n) 3))
    (h3q : Subsingleton (cohomology (gsRoots S q) 3))
    (z : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S q) 3) :
    zmodToQZ n (gsCompactInv S ιs n hKn h3n
        ((compactCohomologyResMap (gsFinFamily S ιs) (gsRootsIncl S hqn) 3).hom z)) =
      zmodToQZ q (gsCompactInv S ιs q hKq h3q z) :=
  zmodToQZ_compactCohomologyResMap_of_localInv (gsFinFamily S ιs) (gsRootsIncl S hqn)
    (gsCompactInv S ιs q hKq h3q) (gsCompactInv S ιs n hKn h3n) (gsLocalInvRootsQZ S ιs q)
    (gsLocalInvRootsQZ S ιs n) (gsLocalInvRootsQZ_comp_gsRootsIncl S ιs hqn)
    (zmodToQZ_gsCompactInv_localToCompact S ιs hKq h3q)
    (zmodToQZ_gsCompactInv_localToCompact S ιs hKn h3n)
    (localToCompact_two_surjective S ιs q h3q) z

end Level

section Hypotheses

variable {N : ℕ} (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)

include hS in

theorem mem_of_natCast_dvd_mem {d : ℕ} (hd : d ∣ N) (v : HeightOneSpectrum (𝓞 K.1))
    (hv : ((d : ℕ) : 𝓞 K.1) ∈ v.asIdeal) : v ∈ S := by
  obtain ⟨c, rfl⟩ := hd
  refine hS v ?_
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

include hK in

theorem odd_or_isTotallyComplex_of_dvd {d : ℕ} (hd : d ∣ N) : Odd d ∨ IsTotallyComplex K.1 :=
  hK.imp (fun ho => ho.of_dvd_nat hd) id

variable [NeZero N] [Fintype S]

theorem gsPoitouTateDualityHypotheses
    (H : ∀ p ∈ N.primeFactors, ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      CompactDualityHypotheses (gsFinFamily S ιs) (p ^ N.factorization p) (gsRoots S (p ^ N.factorization p))
        (gsCompactInv S ιs (p ^ N.factorization p) (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))
          (subsingleton_cohomology_three_gsRoots S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p))
            (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p)))) U₀) :
    PoitouTateDualityHypotheses (gsFinFamily S ιs) (gsRoots S N)
      (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) (gsLocalInvRootsQZ S ιs N) where
  nonempty_addEquiv := nonempty_addEquiv_gsRoots_of_mem S hS
  bijective_compactDualityMap M _ _ hM _ _ h :=
    bijective_compactDualityMap_of_primePow (gsFinFamily S ιs) (gsRoots S N) _
      (fun p => gsRoots S (p ^ N.factorization p))
      (fun p => gsCompactInv S ιs (p ^ N.factorization p) (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))
        (subsingleton_cohomology_three_gsRoots S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p))
          (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))))
      (fun p => gsRootsIncl S (Nat.ordProj_dvd N p)) (nonempty_addEquiv_gsRoots_of_mem S hS)
      (fun p _ => nonempty_addEquiv_gsRoots_of_mem S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p)))
      (fun _ _ => gsRootsIncl_injective S _)
      (fun _ _ z => zmodToQZ_gsCompactInv_gsRootsIncl S ιs _ hK _ _ _ z)
      (fun p hp M _ _ hMp _ _ h => (H p hp).choose_spec.bijective_compactDualityMap M hMp h) M hM h
  finite_cohomology M _ _ hM r := finite_cohomology_gs_of_nsmul S hS hK M hM r
  finite_compactCohomology M _ _ hM r := finite_compactCohomologyRes_gs_of_nsmul S ιs hS hK M hM r
  subsingleton_three M _ _ hM := subsingleton_cohomology_gs_of_nsmul S hS hK M hM le_rfl
  localToCompact_two := zmodToQZ_gsCompactInv_localToCompact S ιs hK _
  surjective_localPairing M _ _ hM v :=
    (bijective_gsLocalPairing S ιs N (nonempty_addEquiv_gsRoots_of_mem S hS) M hM v (show 0 + 2 = 2 from rfl)).2

end Hypotheses

end GroundTheory.ProfCoh
