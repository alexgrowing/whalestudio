import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.GsRootsToUnitsCompactComparisonCup
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh GroundTheory.Global.IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

omit [NeZero n] in
theorem nsmul_zmodToQZ (x : ZMod n) : n • zmodToQZ n x = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

def gsCupClass (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 :=
  compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl)
    ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom (gsUnitsData S ιs d)))
    (cohomologyπ _ 1 z)

def gsLocalUnitsImage (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) (v : S) :
    cohomology (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) 2 :=
  (cohomologyMap (gsRootsOmegaMor S ιs n v ≫ rootsOfUnityToUnits _ _ n) 2).hom (ξ v)

set_option maxHeartbeats 1600000 in

theorem zmodToQZ_gsCompactInv_localToCompact_eq_localInvU (hodd : Odd n ∨ IsTotallyComplex K.1)
    (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    zmodToQZ n (gsCompactInv S ιs n hodd h3
      ((localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom ξ)) =
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalUnitsImage S ιs n ξ v) :=
  (congrArg (zmodToQZ n) ((gsCompactInv_localToCompact S ιs n hodd h3 ξ).trans (gsSumInvRoots_apply S ιs n ξ))).trans
    ((map_sum (zmodToQZ n) _ _).trans
      (Finset.sum_congr rfl fun v _ => zmodToQZ_gsLocalInvRoots_eq_localInvU S ιs n v (ξ v)))

omit [Fintype S] in
set_option maxHeartbeats 1600000 in

theorem gsRootsToUnitsCompact_comparison_localToCompact
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
      ((localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom ξ)) =
      (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
        (gsLocalUnitsImage S ιs n ξ) := by
  have hg : ∀ v, 𝟙 (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v =
      (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (𝟙 (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v :=
    fun _ => Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  have e1 := hom_apply_hom_apply_eq_of_comp_eq (localToCompact_compactCohomologyMap (gsFinFamily S ιs)
    (A := gsRoots S n) (B := gsRoots S n) (Aᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
    (Bᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (a := fun _ => 𝟙 _) (b := gsRootsOmegaMor S ιs n)
    (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n) hg 2) ξ
  have e2 := hom_apply_hom_apply_eq_of_comp_eq (localToCompact_compactCohomologyMap (gsFinFamily S ιs)
    (A := gsRoots S n) (B := galSUnitsMax K.1 ℚ̄ S) (Aᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (Bᵥ := fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (a := gsRootsOmegaMor S ιs n) (b := gsSUnitsLocalMor S ιs)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) 2) (fun v => (cohomologyMap (gsRootsOmegaMor S ιs n v) 2).hom (ξ v))
  refine (congrArg (gsRootsToUnitsCompact S ιs n 3).hom e1).trans (e2.trans ?_)
  refine congrArg (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (gsSUnitsLocalMor S ιs) 2).hom (funext fun v => ?_)
  exact (hom_apply_hom_apply_of_comp_eq (cohomologyMap_comp _ _ 2).symm (ξ v))

def gsLocalCup (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) (v : S) :
    cohomology (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) 2 :=
  cupPairing (mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (show 0 + 2 = 2 from rfl)
    ((H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
    ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))

omit [Fintype S] [NeZero n] in
theorem sub_sub_eq_neg_sub_add {M : Type*} [AddCommGroup M] (a b c : M) : b - (a - c) = -(a - (b + c)) := by
  abel

omit [Fintype S] [NeZero n] in
theorem sum_map_eq_sum_map_sub_add {ι : Type*} (s : Finset ι) {M : ι → Type*} [∀ v, AddCommGroup (M v)] {N : Type*}
    [AddCommGroup N] (F : ∀ v, M v →+ N) (a b : ∀ v, M v) :
    ∑ v ∈ s, F v (a v) = ∑ v ∈ s, F v (a v - b v) + ∑ v ∈ s, F v (b v) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [map_sub, sub_add_cancel]

omit [Fintype S] [NeZero n] in
theorem nsmul_sum_map_sub {ι : Type*} (s : Finset ι) {M : ι → Type*} [∀ v, AddCommGroup (M v)] {N : Type*}
    [AddCommGroup N] (F : ∀ v, M v →+ N) (a b : ∀ v, M v) (ha : ∀ v, n • F v (a v) = 0)
    (hb : ∀ v, n • F v (b v) = 0) : n • ∑ v ∈ s, F v (a v - b v) = 0 := by
  rw [Finset.smul_sum]
  exact Finset.sum_eq_zero fun v _ => by rw [map_sub, smul_sub, ha, hb, sub_zero]

set_option maxHeartbeats 4000000 in

theorem zmodToQZ_gsCompactInv_gsCupClass (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (hχ : ∀ g, Multiplicative.toAdd (χ g) = zmodCocycleHom z g) :
    zmodToQZ n (gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z)) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ (Additive.toMul (gsUnitsClass S d)))) := by
  have hsurj := localToCompact_two_surjective S ιs n h3 (gsCupClass S ιs n hnS d z)
  have hT := (congrArg (fun w => zmodToQZ n (gsCompactInv S ιs n hodd h3 w)) hsurj.choose_spec).symm.trans
    (zmodToQZ_gsCompactInv_localToCompact_eq_localInvU S ιs n hodd h3 hsurj.choose)
  have L1 := gsRootsToUnitsCompact_cup_eq S ιs n hnS ℓ k hℓ hnk hS d z
  have hL2 := (congrArg (fun w => (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom w))
    hsurj.choose_spec).symm.trans (gsRootsToUnitsCompact_comparison_localToCompact S ιs n hsurj.choose)
  have h0 : (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
      (gsLocalUnitsImage S ιs n hsurj.choose - fun v =>
        (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
          (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 L1.choose) + gsLocalCup S ιs n d z v) = 0 := by
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (hL2.symm.trans L1.choose_spec.2))
  have hex := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact_local (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) _ (gsSUnitsLocalMor S ιs) 2) h0
  have hy : ∀ v : S, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 L1.choose) -
        (gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) =
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom (-hex.choose) := fun v =>
    (sub_sub_eq_neg_sub_add _ _ _).trans ((congrArg Neg.neg (congrFun hex.choose_spec v).symm).trans
      (map_neg ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom) hex.choose).symm)
  have hloc : ∀ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalCup S ιs n d z v) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (SIdeleClassGroup.mk S (finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 v)))))) :=
    fun v => localInvU_cupPairing_δ_bockSeq S ιs hodd v (Additive.toMul (d.2 v)) z χ hχ
  have hβ : n • ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1))
      (gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) = 0 :=
    nsmul_sum_map_sub n Finset.univ (fun v : S => localInvU (v : HeightOneSpectrum (𝓞 K.1)))
      (gsLocalUnitsImage S ιs n hsurj.choose) (gsLocalCup S ιs n d z)
      (fun v => (congrArg (n • ·) (zmodToQZ_gsLocalInvRoots_eq_localInvU S ιs n v (hsurj.choose v)).symm).trans
        (nsmul_zmodToQZ n _))
      (fun v => (congrArg (n • ·) (hloc v)).trans (nsmul_zmodToQZ n _))
  have hT1 := sum_localInvU_eq_neg_divChar S ιs hodd (Additive.toMul d.1) z χ hχ L1.choose L1.choose_spec.1
    (fun v => gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) (-hex.choose) hy hβ
  have hsum : ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalUnitsImage S ιs n hsurj.choose v) =
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1))
        (gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) +
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalCup S ιs n d z v) :=
    sum_map_eq_sum_map_sub_add Finset.univ (fun v : S => localInvU (v : HeightOneSpectrum (𝓞 K.1)))
      (gsLocalUnitsImage S ιs n hsurj.choose) (gsLocalCup S ιs n d z)
  exact hT.trans (hsum.trans ((congrArg₂ (· + ·) hT1 (Finset.sum_congr rfl fun v _ => hloc v)).trans
    ((neg_add_eq_sub _ _).trans (zmodToQZ_charEquiv_gsUnitsClass S n hodd χ d).symm)))

end

end GroundTheory.ProfCoh
