import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealLocal
import GroundTheory.ProfiniteCohomology.PoitouTate.RealCup
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import GroundTheory.ProfiniteCohomology.Colimit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory CategoryTheory.Limits MonoidalCategory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section OrderTwoOdd

variable {F : Type} [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [Fintype F] {n : ℕ}
  (hn : Odd n) (B : Rep.{0} (ULift.{0} ℤ) F) [IsDiscreteRep B] (hB : ∀ b : B, n • b = 0)

include hn hB in

theorem isZero_cohomology_of_card_two_of_odd [CompactSpace F] [TotallyDisconnectedSpace F]
    (hcard : Fintype.card F = 2) (m : ℕ) : IsZero (cohomology B (m + 1)) := by
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  have hz : ∀ x : cohomology B (m + 1), x = 0 := by
    intro x
    have hnx : n • x = 0 := nsmul_cohomology_eq_zero B hB (m + 1) x
    obtain ⟨U, hU⟩ := exists_card_smul_eq_zero B (Nat.succ_ne_zero m) x
    have hdvd : Nat.card (F ⧸ (U : Subgroup F)) ∣ 2 := by
      rw [← hcard, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_quotient_dvd_card _
    obtain ⟨d, hd⟩ := hdvd
    have h2x : 2 • x = 0 := by rw [hd, mul_comm, mul_nsmul', hU, nsmul_zero]
    obtain ⟨k, rfl⟩ := hn
    calc x = (2 * k + 1) • x - (k * 2) • x := by
          rw [mul_comm k 2, add_nsmul, one_nsmul, add_sub_cancel_left]
      _ = 0 := by rw [hnx, mul_nsmul', h2x, nsmul_zero, sub_zero]
  rw [hz x, hz y]

omit [TopologicalSpace F] [IsTopologicalGroup F] [IsDiscreteRep B] in
include hn hB in

theorem exists_norm_of_orderTwo_of_odd {c : F} (hG : ∀ g : F, g = 1 ∨ g = c) (hc : c ≠ 1) :
    ∀ x ∈ B.ρ.invariants, ∃ m, B.ρ.norm m = x := by
  intro x hx
  obtain ⟨k, hk⟩ := hn
  refine ⟨(k + 1) • x, ?_⟩
  rw [OrderTwo.norm_apply B hG hc, map_nsmul, hx c, ← add_nsmul]
  have h : k + 1 + (k + 1) = n + 1 := by omega
  rw [h, add_nsmul, one_nsmul, hB, zero_add]

end OrderTwoOdd

section Local

variable {n : ℕ} (hn : Odd n) (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep A]
  (hA : ∀ a : A, n • a = 0)

include hn hA in

theorem isZero_cohomology_gsReal_of_odd (w : {v : InfinitePlace K.1 // v.IsReal}) (m : ℕ) :
    IsZero (cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom A) (m + 1)) := by
  have key := isZero_cohomology_of_card_two_of_odd hn (Rep.res (gsRealFamily S ιr w).toMonoidHom A) hA
    ?hcard m
  case hcard => exact card_realGal_eq_two w.1 w.2
  exact key

omit [IsDiscreteRep A] in
include hn hA in

theorem exists_norm_gsReal_of_odd (w : {v : InfinitePlace K.1 // v.IsReal}) :
    ∀ x ∈ (Rep.res (gsRealFamily S ιr w).toMonoidHom A).ρ.invariants,
      ∃ m, (Rep.res (gsRealFamily S ιr w).toMonoidHom A).ρ.norm m = x := by
  have key := exists_norm_of_orderTwo_of_odd hn (Rep.res (gsRealFamily S ιr w).toMonoidHom A) hA
    (c := realConj w.1 w.2) ?hG ?hc
  case hG => exact eq_one_or_eq_realConj w.1 w.2
  case hc => exact realConj_ne_one w.1 w.2
  exact key

include hn hA in

theorem bijective_tateForget_gs_of_odd (m : ℕ) :
    Function.Bijective (tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) A
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom A) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom A) (fun _ => 𝟙 _) (m + 1)).hom := by
  have := isIso_tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) A
    (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom A) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom A) (fun _ => 𝟙 _)
    (fun w m => isZero_cohomology_gsReal_of_odd S ιr hn A hA w m)
    (fun w => exists_norm_gsReal_of_odd S ιr hn A hA w) m
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

include hn hA in

theorem bijective_tateForget_gs_of_odd' {m : ℕ} (hm : 1 ≤ m) :
    Function.Bijective (tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) A
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom A) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom A) (fun _ => 𝟙 _) m).hom := by
  cases m with
  | zero => exact absurd hm (by norm_num)
  | succ m => exact bijective_tateForget_gs_of_odd S ιr ιs hn A hA m

end Local

section Hypotheses

noncomputable instance fintypeRealPlaces (K : FiniteSubfield) : Fintype {v : InfinitePlace K.1 // v.IsReal} :=
  Fintype.ofFinite _

theorem injective_resZero {G H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →ₜ* G)
    (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] :
    Function.Injective (cohomologyMapAlong φ.toMonoidHom (continuous_toMonoidHom φ)
      (𝟙 (Rep.res φ.toMonoidHom M)) 0).hom := by
  intro x y h
  have ex := H0Iso_hom_cohomologyMapAlong φ.toMonoidHom (continuous_toMonoidHom φ) (𝟙 _) x
  have ey := H0Iso_hom_cohomologyMapAlong φ.toMonoidHom (continuous_toMonoidHom φ) (𝟙 _) y
  rw [h] at ex
  have hxy' : (H0Iso M).hom.hom x = (H0Iso M).hom.hom y := Subtype.ext (ex.symm.trans ey)
  calc x = (H0Iso M).inv.hom ((H0Iso M).hom.hom x) :=
        (hom_apply_hom_apply_of_comp_eq (H0Iso M).hom_inv_id x).symm
    _ = (H0Iso M).inv.hom ((H0Iso M).hom.hom y) := by rw [hxy']
    _ = y := hom_apply_hom_apply_of_comp_eq (H0Iso M).hom_inv_id y

theorem injective_ptRes_zero_gs [Nonempty S] (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] : Function.Injective fun (x : cohomology M 0) v => ptRes (gsFinFamily S ιs) M v 0 x :=
  fun x y hxy => (‹Nonempty S›.elim fun v =>
    injective_resZero (gsFinFamily S ιs v) M (congrFun hxy v))

variable [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hodd : Odd N)

def gsOddTrace : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N :=
  (gsCompactInv S ιs N (Or.inl hodd) (subsingleton_cohomology_three_gsRoots S hS (Or.inl hodd))).comp
    (tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _) 3).hom.toAddMonoidHom

omit [Fintype S] [NeZero N] in
include hodd in

theorem gsReal_two_eq_zero_of_odd (w : {v : InfinitePlace K.1 // v.IsReal})
    (x : cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) 2) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero
    (isZero_cohomology_gsReal_of_odd S ιr hodd (gsRoots S N) (nsmul_gsRoots S N) w 1)).elim _ _

theorem gsOddTrace_apply (z : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3) :
    gsOddTrace S ιr ιs hS hodd z =
      gsCompactInv S ιs N (Or.inl hodd) (subsingleton_cohomology_three_gsRoots S hS (Or.inl hodd))
        ((tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
          (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _)
          (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _) 3).hom z) :=
  rfl

set_option maxHeartbeats 1000000 in

theorem gsOddTrace_localToCompact
    (ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2) :
    zmodToQZ N (gsOddTrace S ιr ιs hS hodd ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr)
      (gsRoots S N) 2).hom ξ)) =
      ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w) := by
  have h1 : (tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _) 3).hom
        ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ) =
      (localToCompact (gsFinFamily S ιs) (gsRoots S N) _ (fun _ => 𝟙 _) 2).hom ξ.1 :=
    congrArg (fun f => f.hom ξ) (tateLocalToCompact_tateForget (gsFinFamily S ιs) (gsRealFamily S ιr)
      (gsRoots S N) (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _) 2)
  have h2 : ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w) = 0 :=
    Finset.sum_eq_zero fun w _ =>
      (congrArg (gsRealInvRootsQZ S ιr N w) (gsReal_two_eq_zero_of_odd S ιr hodd w (ξ.2 w))).trans (map_zero _)
  calc zmodToQZ N (gsOddTrace S ιr ιs hS hodd ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr)
        (gsRoots S N) 2).hom ξ))
      = ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) :=
        (congrArg (zmodToQZ N) ((gsOddTrace_apply S ιr ιs hS hodd _).trans (congrArg _ h1))).trans
          (zmodToQZ_gsCompactInv_localToCompact S ιs (Or.inl hodd) _ ξ.1)
    _ = ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + 0 := (add_zero _).symm
    _ = _ := congrArg (∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ·) h2.symm

set_option maxHeartbeats 1000000 in
include hS in

theorem bijective_tateCompactDualityMap_gs_of_odd (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h
      (gsOddTrace S ιr ιs hS hodd) M) := by
  have hf := bijective_tateForget_gs_of_odd' S ιr ιs hodd (dualRep (gsRoots S N) M)
    (nsmul_dualRep_eq_zero (nsmul_gsRoots S N)) hs
  have hγ := poitouTate_duality_gs S ιs hS (Or.inl hodd) M hM h
  refine bijective_of_bijective_precomp _ _ (AddEquiv.ofBijective _ hf) (fun x y => ?_) hγ
  exact (gsOddTrace_apply S ιr ιs hS hodd _).trans (congrArg _ (tateForget_tateCompactCupRes
    (gsFinFamily S ιs) (gsRealFamily S ιr) (dualEvalPairing (gsRoots S N) M) _ y x))

include hS hodd in

theorem gsOddTatePoitouTateHypotheses [Nonempty S] :
    TatePoitouTateHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (gsOddTrace S ιr ιs hS hodd) (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) := by
  have hD := nonempty_addEquiv_gsRoots_of_mem S hS
  exact
    { nonempty_addEquiv := hD
      duality := @fun M _ _ hM r s h hs => bijective_tateCompactDualityMap_gs_of_odd S ιr ιs hS hodd M hM h hs
      finite_cohomology := fun M _ _ hM r hr =>
        finite_cohomology_gs K S M (fun v hv => hS v (natCast_mem_of_natCard_mem v.isPrime hM hv)) r hr
      localToCompact_two := gsOddTrace_localToCompact S ιr ιs hS hodd
      injective_res_zero := fun M _ => injective_ptRes_zero_gs S ιs M
      surjective_localPairing_zero := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_localPairing_two := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_realPairing_zero := fun M _ _ hM w => surjective_gsRealPairing_zero S ιr N M hD hM w
      surjective_realPairing_two := fun M _ _ hM w χ hχ => exists_gsRealPairing_two S ιr N M hD hM w χ hχ }

end Hypotheses

end GroundTheory.ProfCoh
