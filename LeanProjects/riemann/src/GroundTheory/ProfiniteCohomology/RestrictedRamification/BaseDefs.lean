import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SumInvariants
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section ULiftCompare

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {A B : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep A]
  [IsDiscreteRep B] {C : Rep.{0} ℤ H} [IsDiscreteRep C] [IsDiscreteRep (Rep.res φ A)]
  [IsDiscreteRep (uliftIntToIntRep (Rep.res φ A))]

theorem cohomologyMap_uliftInt_cohomologyMapAlong {A' : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep A']
    (g₁ : A ⟶ A') (g₂ : A' ⟶ B)
    (f₁ : uliftIntToIntRep (Rep.res φ A) ⟶ C) (f₂ : Rep.res φ (uliftIntToIntRep B) ⟶ C)
    (hf : ∀ a : A, f₁.hom a = f₂.hom (g₂.hom (g₁.hom a))) (m : ℕ) (x : cohomology A m) :
    (cohomologyMap f₁ m).hom (cohomologyULiftIntAddEquiv _ m
        ((cohomologyMapAlong φ hφ (𝟙 (Rep.res φ A)) m).hom x)) =
      (cohomologyMapAlong φ hφ f₂ m).hom (cohomologyULiftIntAddEquiv _ m
        ((cohomologyMap g₂ m).hom ((cohomologyMap g₁ m).hom x))) := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A m x
  rw [cohomologyMapAlong_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMap_cohomologyπ,
    cohomologyMap_cohomologyπ, cohomologyMap_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ',
    cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cocyclesULiftInt, cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cyclesMap]
  funext h
  exact hf _

end ULiftCompare

section Descend

variable {R G Q M : Type*} [Ring R] {_ : AddCommGroup G} {_ : AddCommGroup Q} [AddCommGroup M]
  {_ : Module R G} {_ : Module R Q}

noncomputable def descendAlong (f : G →ₗ[R] Q) (hf : Function.Surjective f) (φ : G →+ M)
    (h : f.toAddMonoidHom.ker ≤ φ.ker) : Q →+ M :=
  (QuotientAddGroup.lift _ φ h).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective f.toAddMonoidHom hf).symm.toAddMonoidHom

theorem descendAlong_apply (f : G →ₗ[R] Q) (hf : Function.Surjective f) (φ : G →+ M)
    (h : f.toAddMonoidHom.ker ≤ φ.ker) (g : G) : descendAlong f hf φ h (f g) = φ g := by
  have e : (QuotientAddGroup.quotientKerEquivOfSurjective f.toAddMonoidHom hf).symm (f g) =
      (g : G ⧸ f.toAddMonoidHom.ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  change QuotientAddGroup.lift _ φ h
    ((QuotientAddGroup.quotientKerEquivOfSurjective f.toAddMonoidHom hf).symm (f g)) = φ g
  rw [e]
  rfl

end Descend

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))

abbrev gsRoots (n : ℕ) : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S) :=
  galRootsOfUnity K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n

instance isDiscreteRep_gsRoots (n : ℕ) : IsDiscreteRep (gsRoots S n) :=
  isDiscreteRep_galRootsOfUnity n

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n : ℕ)

instance isDiscreteRep_res_gsRoots (v : S) :
    IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) :=
  isDiscreteRep_res_toMonoidHom (gsFinFamily S ιs v) (gsRoots S n)

instance isDiscreteRep_uliftIntToIntRep_res_gsRoots (v : S) :
    IsDiscreteRep (uliftIntToIntRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))) :=
  ⟨fun a => isOpen_stabilizer (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) a⟩

def rootsLocalMorZ (v : S) :
    uliftIntToIntRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) ⟶
      galUnitsZ ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      ((Units.map ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom.toMonoidHom).comp
        (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)).subtype)).toIntLinearMap,
    fun σ => LinearMap.ext fun ζ => congrArg Additive.ofMul
      (Units.ext (gsFinFamily_apply S ιs v σ
        (((Additive.toMul ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
          maxUnramifiedOutside K.1 ℚ̄ S)))⟩

@[simp]
theorem rootsLocalMorZ_hom_apply (v : S) (ζ : Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) :
    ((Additive.toMul ((rootsLocalMorZ S ιs n v).hom ζ) :
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ) :
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) =
      ιs v (((Additive.toMul ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : ℚ̄) :=
  rfl

def gsLocalInvRootsQZ (v : S) :
    cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2 →+ QZ :=
  (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).comp
    ((cohomologyMap (rootsLocalMorZ S ιs n v) 2).hom.toAddMonoidHom.comp
      (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom)

theorem nsmul_gsRoots (ζ : gsRoots S n) : n • ζ = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((Additive.toMul ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^ n = 1
  exact (mem_rootsOfUnity n _).1 (Additive.toMul ζ).2

theorem nsmul_gsLocalInvRootsQZ (v : S)
    (y : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    n • gsLocalInvRootsQZ S ιs n v y = 0 := by
  have h : n • y = 0 := nsmul_cohomology_eq_zero (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
    (fun ζ => nsmul_gsRoots S n ζ) 2 y
  exact (map_nsmul (gsLocalInvRootsQZ S ιs n v) n y).symm.trans
    ((congrArg (gsLocalInvRootsQZ S ιs n v) h).trans (map_zero _))

variable [NeZero n]

def gsLocalInvRoots (v : S) :
    cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2 →+ ZMod n :=
  zmodOfQZ (gsLocalInvRootsQZ S ιs n v) (nsmul_gsLocalInvRootsQZ S ιs n v)

theorem zmodToQZ_gsLocalInvRoots (v : S)
    (y : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    zmodToQZ n (gsLocalInvRoots S ιs n v y) = gsLocalInvRootsQZ S ιs n v y :=
  zmodToQZ_zmodOfQZ _ _ y

variable [Fintype S]

def gsSumInvRoots :
    ModuleCat.of (ULift.{0} ℤ) (∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) →+
      ZMod n where
  toFun ξ := ∑ v : S, gsLocalInvRoots S ιs n v (ξ v)
  map_zero' := Finset.sum_eq_zero fun _ _ => map_zero _
  map_add' _ _ := (Finset.sum_congr rfl fun _ _ => map_add _ _ _).trans Finset.sum_add_distrib

theorem gsSumInvRoots_apply
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    gsSumInvRoots S ιs n ξ = ∑ v : S, gsLocalInvRoots S ιs n v (ξ v) := by
  rfl

omit [Fintype S] [NeZero n] in
theorem gsLocalInvRootsQZ_eq (v : S) :
    gsLocalInvRootsQZ S ιs n v =
      (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).comp
        ((cohomologyMap (rootsLocalMorZ S ιs n v) 2).hom.toAddMonoidHom.comp
          (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom) :=
  rfl

omit [Fintype S] in

theorem gsLocalInvRootsQZ_cohomologyMapAlong (v : S) (x : cohomology (gsRoots S n) 2) :
    gsLocalInvRootsQZ S ιs n v ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
        (continuous_toMonoidHom _) (𝟙 _) 2).hom x) =
      brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ((gsLocalRes S (ιs v) 2).hom
        (cohomologyULiftIntAddEquiv _ 2 ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom
          ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n) 2).hom x)))) := by
  refine (DFunLike.congr_fun (gsLocalInvRootsQZ_eq S ιs n v) _).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine congrArg (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  exact cohomologyMap_uliftInt_cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
    (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n) (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))
    (rootsLocalMorZ S ιs n v) (embUnitsMorZ S (ιs v)) (fun _ => rfl) 2 x

omit [Fintype S] [NeZero n] in

theorem placeInv_inl_eq_zero (hn : Odd n ∨ IsTotallyComplex K.1) (v : InfinitePlace K.1)
    (y : localGaloisCohomology K 2 (.inl v)) (hy : n • y = 0) : placeInv (.inl v) y = 0 := by
  rcases hn with ⟨m, rfl⟩ | hc
  · have h2 : 2 • y = 0 := by
      apply placeInv_injective (K := K) (.inl v)
      rw [map_nsmul, map_zero]
      by_cases hy0 : y = 0
      · rw [hy0, map_zero, smul_zero]
      · change 2 • quadraticInvFun v.Completion (AlgebraicClosure v.Completion) y = 0
        rw [quadraticInvFun_of_ne_zero _ _ hy0, two_nsmul, QZ.mk_half_add_mk_half]
    have hy' : y = (2 * m + 1) • y - m • (2 • y) := by
      rw [← mul_nsmul', add_nsmul, one_nsmul, mul_comm m 2]
      abel
    rw [hy', hy, h2, smul_zero, sub_zero, map_zero]
  · have := subsingleton_cohomology_two_of_isComplex v (hc.isComplex v)
    rw [show y = 0 from Subsingleton.elim (α := cohomology (galUnitsZ v.Completion
      (AlgebraicClosure v.Completion)) 2) y 0, map_zero]

omit [Fintype S] in

theorem sumPlaceInv_eq_sum_of_placeInv (T : Finset (Place K.1)) (y : ⨁ w : Place K.1, localGaloisCohomology K 2 w)
    (hT : ∀ w ∉ T, placeInv w (y w) = 0) : sumPlaceInv K y = ∑ w ∈ T, placeInv w (y w) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of y]
  rw [map_sum]
  simp_rw [sumPlaceInv_of]
  calc ∑ w ∈ DFinsupp.support y, placeInv w (y w)
      = ∑ w ∈ DFinsupp.support y ∪ T, placeInv w (y w) :=
        Finset.sum_subset Finset.subset_union_left fun w _ hw => by
          rw [DFinsupp.notMem_support_iff.1 hw, map_zero]
    _ = ∑ w ∈ T, placeInv w (y w) :=
        (Finset.sum_subset Finset.subset_union_right fun w _ hw => hT w hw).symm

omit [Fintype S] [NeZero n] in

theorem placeInv_inr_apply (v : HeightOneSpectrum (𝓞 K.1)) (y : localGaloisCohomology K 2 (.inr v)) :
    placeInv (.inr v) y = brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) y :=
  rfl

open Classical in

def gsLocalEmbeddings : LocalEmbeddings K where
  fin v := if h : v ∈ S then ιs ⟨v, h⟩ else (nonempty_localEmbeddings K).some.fin v
  inf v := (nonempty_localEmbeddings K).some.inf v

omit [Fintype S] [NeZero n] in
theorem gsLocalEmbeddings_fin (v : S) : (gsLocalEmbeddings S ιs).fin v = ιs v :=
  dif_pos v.2

omit [Fintype S] in

theorem sum_eq_zero_of_zmodToQZ {ι : Type*} [Fintype ι] (F : ι → ZMod n) (G : ι → QZ)
    (hFG : ∀ v, zmodToQZ n (F v) = G v) (h : ∑ v, G v = 0) : ∑ v, F v = 0 :=
  zmodToQZ_injective (by rw [map_sum, map_zero, ← h]; exact Finset.sum_congr rfl fun v _ => hFG v)

omit [NeZero n] in

theorem brauerSumInv_eq_sum_of (ι : LocalEmbeddings K) (z : cohomology (unitsLimitRep K) 2)
    (hz : ∀ w : Place K.1, (∀ v : S, w ≠ .inr (v : HeightOneSpectrum (𝓞 K.1))) →
      placeInv w (brauerLocal ι z w) = 0) :
    brauerSumInv ι z = ∑ v : S, placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      (brauerLocal ι z (.inr (v : HeightOneSpectrum (𝓞 K.1)))) := by
  classical
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  rw [sumPlaceInv_eq_sum_of_placeInv (Finset.univ.image fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1))
      _ fun w hw => hz w fun v hv => hw (Finset.mem_image.2 ⟨v, Finset.mem_univ _, hv.symm⟩),
    Finset.sum_image (fun v _ w _ h => Subtype.ext (Sum.inr_injective h))]

omit [NeZero n] in

theorem sum_brauerInvZ_gsLocalRes_sUnits (hn : Odd n ∨ IsTotallyComplex K.1)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) (hy : n • y = 0) :
    ∑ v : S, brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ((gsLocalRes S (ιs v) 2).hom
        (cohomologyULiftIntAddEquiv _ 2
          ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y))) = 0 := by
  have h1 := brauerSumInv_eq_sum_of S (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) ?_
  · refine (Finset.sum_congr rfl fun v _ => ?_).trans (h1.symm.trans
      (brauerSumInv_eq_zero (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y)))
    refine Eq.symm ?_
    refine (congrArg (fun z => placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      (brauerLocal (gsLocalEmbeddings S ιs) z (.inr (v : HeightOneSpectrum (𝓞 K.1))))) (sUnitsBrauer_apply K S y)).trans ?_
    refine (congrArg (placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))))
      (brauerLocal_gsBrauerInfl_inr K S _ _ _)).trans ?_
    refine (placeInv_inr_apply _ _).trans ?_
    simp only [gsLocalEmbeddings_fin]
  · intro w hw
    rcases w with w | w
    · refine placeInv_inl_eq_zero n hn w _ ?_
      calc n • brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) (.inl w)
          = DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w) (Sum.inl w : Place K.1)
              (n • brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y)) :=
            (map_nsmul (DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w) (Sum.inl w : Place K.1)) n
              (brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y))).symm
        _ = 0 := by rw [← map_nsmul, ← map_nsmul, hy, map_zero, map_zero, map_zero]
    · have hwS : w ∉ S := fun h => hw ⟨w, h⟩ rfl
      rw [brauerLocal_sUnitsBrauer_inr K S (gsLocalEmbeddings S ιs) y w hwS, map_zero]

theorem gsSumInvRoots_globalToLocal (hn : Odd n ∨ IsTotallyComplex K.1) (x : cohomology (gsRoots S n) 2) :
    gsSumInvRoots S ιs n ((globalToLocal (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom x) = 0 := by
  refine (gsSumInvRoots_apply S ιs n _).trans (sum_eq_zero_of_zmodToQZ n _ _ (fun v =>
    (zmodToQZ_gsLocalInvRoots S ιs n v _).trans (gsLocalInvRootsQZ_cohomologyMapAlong S ιs n v x))
    (sum_brauerInvZ_gsLocalRes_sUnits S ιs n hn _ ?_))
  rw [← map_nsmul, nsmul_cohomology_eq_zero _ (fun ζ => nsmul_gsRoots S n ζ) 2 x, map_zero]

omit [Fintype S] [NeZero n] in

theorem localToCompact_two_surjective (h3 : Subsingleton (cohomology (gsRoots S n) 3)) :
    Function.Surjective (localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom := fun _ =>
  (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact_compact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2)
    (Subsingleton.elim (α := cohomology (gsRoots S n) 3) _ _)

theorem ker_localToCompact_le (hn : Odd n ∨ IsTotallyComplex K.1) :
    (localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom.toAddMonoidHom.ker ≤
      (gsSumInvRoots S ιs n).ker := fun ξ hξ => by
  have h := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact_local (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2) hξ
  obtain ⟨x, hx⟩ := h
  exact hx ▸ gsSumInvRoots_globalToLocal S ιs n hn x

noncomputable def gsCompactInv (hn : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3)) :
    compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 →+ ZMod n :=
  descendAlong (localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom
    (localToCompact_two_surjective S ιs n h3) (gsSumInvRoots S ιs n) (ker_localToCompact_le S ιs n hn)

set_option maxHeartbeats 1600000 in

theorem gsCompactInv_localToCompact (hn : Odd n ∨ IsTotallyComplex K.1)
    (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    gsCompactInv S ιs n hn h3 ((localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom ξ) =
      gsSumInvRoots S ιs n ξ :=
  descendAlong_apply (localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom
    (localToCompact_two_surjective S ιs n h3) (gsSumInvRoots S ιs n) (ker_localToCompact_le S ιs n hn) ξ

end

end GroundTheory.ProfCoh
