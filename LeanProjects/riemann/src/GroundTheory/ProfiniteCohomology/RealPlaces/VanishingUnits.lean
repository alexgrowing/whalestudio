import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingUnitsDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Setup

abbrev finUnitsMor (v : S) :=
  sUnitsLocalMor S (gsFinFamily S ιs v).toMonoidHom
    ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιs v))

abbrev realUnitsMor (w : {v : InfinitePlace K.1 // v.IsReal}) :=
  sUnitsLocalMor S (gsRealFamily S ιr w).toMonoidHom
    ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιr w))

abbrev finUnits (v : S) : Rep.{0} (ULift.{0} ℤ)
    Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) /
      (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) :=
  galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

abbrev realUnits (w : {v : InfinitePlace K.1 // v.IsReal}) :
    Rep.{0} (ULift.{0} ℤ) Gal(AlgebraicClosure w.1.Completion / w.1.Completion) :=
  galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)

instance isDiscreteRep_finUnits (v : S) : IsDiscreteRep (finUnits S v) :=
  isDiscreteRep_galUnits (K := (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (L := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

instance isDiscreteRep_realUnits (w : {v : InfinitePlace K.1 // v.IsReal}) : IsDiscreteRep (realUnits w) :=
  isDiscreteRep_galUnits (K := w.1.Completion) (L := AlgebraicClosure w.1.Completion)

abbrev unitsTateCohomology (n : ℕ) : ModuleCat (ULift.{0} ℤ) :=
  tateCompactCohomology (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
    (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) n

theorem subsingleton_finLocal (v : S) {n : ℕ} (hn : 3 ≤ n) :
    Subsingleton (cohomology (galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) n) :=
  subsingleton_cohomology_galUnits_of_three_le _ _ hn

abbrev realLocalEquiv (w : {v : InfinitePlace K.1 // v.IsReal}) (n : ℕ) :
    cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) n ≃+
      localGaloisCohomology K n (.inl w.1) :=
  cohomologyULiftIntAddEquiv (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) n

abbrev finLocalEquiv (v : HeightOneSpectrum (𝓞 K.1)) (n : ℕ) :
    cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) n ≃+
      localGaloisCohomology K n (.inr v) :=
  cohomologyULiftIntAddEquiv (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) n

theorem subsingleton_realLocal_of_odd (w : {v : InfinitePlace K.1 // v.IsReal}) {n : ℕ} (hn : Odd n) :
    Subsingleton (cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) n) := by
  have := subsingleton_localGaloisCohomology_of_isReal_of_odd w.1 w.2 hn
  exact (realLocalEquiv w n).injective.subsingleton

set_option maxHeartbeats 1000000 in

theorem two_nsmul_realLocal (w : {v : InfinitePlace K.1 // v.IsReal}) {n : ℕ} (hn : 1 ≤ n)
    (t : cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) n) : 2 • t = 0 := by
  rcases Nat.even_or_odd n with he | ho
  · have hc := natCard_localGaloisCohomology_of_isReal_of_even w.1 w.2 (by omega) he
    have : Finite (localGaloisCohomology K n (.inl w.1)) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    apply (realLocalEquiv w n).injective
    rw [map_nsmul, map_zero]
    have h := card_nsmul_eq_zero' (G := localGaloisCohomology K n (.inl w.1)) (x := realLocalEquiv w n t)
    rw [hc] at h
    exact h
  · have := subsingleton_realLocal_of_odd w ho
    exact Subsingleton.elim _ _

end Setup

section Real

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

abbrev realUnitsRes (r : ℕ) (w : {v : InfinitePlace K.1 // v.IsReal}) :
    cohomology (galSUnitsMax K.1 ℚ̄ S) r ⟶
      cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) r :=
  cohomologyMapAlong (gsRealFamily S ιr w).toMonoidHom (continuous_toMonoidHom _) (realUnitsMor S ιr w) r

theorem realUnitsRes_eq (r : ℕ) (w : {v : InfinitePlace K.1 // v.IsReal}) :
    realUnitsRes S ιr r w =
      cohomologyMapAlong (decompHomS w.1.Completion S (ιr w)) (continuous_decompHomS (Kv := w.1.Completion) S (ιr w))
        (sUnitsLocalMor S (decompHomS w.1.Completion S (ιr w))
          ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιr w))) r :=
  rfl

theorem realLocalEquiv_realUnitsRes (ι : LocalEmbeddings K) {r : ℕ} (hr : 1 ≤ r)
    (w : {v : InfinitePlace K.1 // v.IsReal}) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) r) :
    realLocalization ι hr (sUnitsInfl K S r y) w = realLocalEquiv w r ((realUnitsRes S ιr r w).hom y) := by
  refine (idelesLimitCohomologyEquiv_unitsToIdeles_inl ι hr w.1 (sUnitsInfl K S r y)).trans ?_
  refine (congrArg (fun f => f.hom (sUnitsInfl K S r y))
    (unitsLocalRes_eq_of_algHom w.1.Completion (ιr w) (ι.inf w.1) r)).trans ?_
  exact (unitsLocalRes_sUnitsInfl S (ιr w) r y).trans
    (congrArg (realLocalEquiv w r) (congrArg (fun f => f.hom y) (realUnitsRes_eq S ιr r w).symm))

set_option maxHeartbeats 1000000 in
include h2S in

theorem eq_zero_of_realUnitsRes_eq_zero {r : ℕ} (hr : 4 ≤ r) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) r)
    {k : ℕ} (hk : 2 ^ k • y = 0) (h : ∀ w, (realUnitsRes S ιr r w).hom y = 0) : y = 0 := by
  have hinj := (sUnitsRealPrimaryEquiv K S (nonempty_localEmbeddings K).some h2S hr).injective
  have h0 : (⟨y, k, hk⟩ : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) 2) = 0 := by
    apply hinj
    rw [map_zero]
    funext w
    rw [sUnitsRealPrimaryEquiv_apply, realLocalEquiv_realUnitsRes S ιr (nonempty_localEmbeddings K).some (by omega) w y, h w, map_zero]
    rfl
  exact congrArg Subtype.val h0

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_realUnitsRes_eq {r : ℕ} (hr : 4 ≤ r)
    (t : ∀ w : {v : InfinitePlace K.1 // v.IsReal},
      cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) r) :
    ∃ y, ∀ w, (realUnitsRes S ιr r w).hom y = t w := by
  obtain ⟨⟨y, _⟩, hy⟩ := (sUnitsRealPrimaryEquiv K S (nonempty_localEmbeddings K).some h2S hr).surjective
    (fun w => realLocalEquiv w r (t w))
  refine ⟨y, fun w => (realLocalEquiv w r).injective ?_⟩
  rw [← realLocalEquiv_realUnitsRes S ιr (nonempty_localEmbeddings K).some (by omega) w y]
  rw [sUnitsRealPrimaryEquiv_apply] at hy
  exact congrFun hy w

set_option maxHeartbeats 1000000 in

theorem realUnitsRes_tateToGlobal (n : ℕ) (x : unitsTateCohomology S ιr ιs (n + 1))
    (w : {v : InfinitePlace K.1 // v.IsReal}) :
    (realUnitsRes S ιr (n + 1) w).hom ((tateToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr)
      (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (n + 1)).hom x) =
        0 :=
  congrFun (congrArg Prod.snd (hom_apply_hom_apply_of_comp_eq (tateToGlobal_tateGlobalToLocal
    (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs) realUnits
    (realUnitsMor S ιr) n) x)) w

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_realUnitsRes_eq_of_three_le {m : ℕ} (hm : 3 ≤ m + 1)
    (t : ∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) (m + 1)) :
    ∃ y : cohomology (galSUnitsMax K.1 ℚ̄ S) (m + 1), ∀ w, (realUnitsRes S ιr (m + 1) w).hom y = t w := by
  rcases Nat.even_or_odd (m + 1) with he | ho
  · exact exists_realUnitsRes_eq S ιr h2S (r := m + 1) (by obtain ⟨j, hj⟩ := he; omega) t
  · exact ⟨0, fun w => @Subsingleton.elim _ (subsingleton_realLocal_of_odd w ho) _ _⟩

set_option maxHeartbeats 2000000 in

theorem tateGlobalToLocal_units_eq {m : ℕ} (hm : 3 ≤ m + 1)
    (t : (∀ v : S, cohomology (finUnits S v) (m + 1)) ×
      (∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) (m + 1)))
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) (m + 1)) (hy : ∀ w, (realUnitsRes S ιr (m + 1) w).hom y = t.2 w) :
    (tateGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
      (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (m + 1)).hom y = t := by
  have h1 : (globalToLocal (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs)
      (m + 1)).hom y = t.1 := funext fun v => @Subsingleton.elim _ (subsingleton_finLocal S v hm) _ _
  exact Prod.ext h1 (funext hy)

include h2S in

theorem exists_tateGlobalToLocal_eq {m : ℕ} (hm : 3 ≤ m + 1)
    (t : (∀ v : S, cohomology (finUnits S v) (m + 1)) ×
      (∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) (m + 1))) :
    ∃ g : cohomology (galSUnitsMax K.1 ℚ̄ S) (m + 1),
      (tateGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
        (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (m + 1)).hom g = t :=
  (exists_realUnitsRes_eq_of_three_le S ιr h2S hm t.2).imp fun y hy =>
    tateGlobalToLocal_units_eq S ιr ιs hm t y hy

set_option maxHeartbeats 1000000 in
include h2S in

theorem tateToGlobal_units_eq_zero {n : ℕ} (hn : 3 ≤ n) (x : unitsTateCohomology S ιr ιs (n + 1))
    {k : ℕ} (hk : 2 ^ k • x = 0) :
    (tateToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
      (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (n + 1)).hom x = 0 := by
  refine eq_zero_of_realUnitsRes_eq_zero S ιr h2S (by omega) _ (k := k) ?_ fun w => ?_
  · rw [← map_nsmul, hk, map_zero]
  · exact realUnitsRes_tateToGlobal S ιr ιs n x w

set_option maxHeartbeats 1000000 in
include h2S in

theorem eq_zero_of_tateToGlobal_units_eq_zero {m : ℕ} (hm : 3 ≤ m + 1)
    (x : unitsTateCohomology S ιr ιs (m + 1 + 1))
    (hx : (tateToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
      (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (m + 1 + 1)).hom x = 0) : x = 0 := by
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).1 (tateCompactCohomology_exact_compact
    (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs)
    realUnits (realUnitsMor S ιr) (m + 1)) x hx
  obtain ⟨g, hg⟩ := exists_tateGlobalToLocal_eq S ιr ιs h2S hm t
  rw [← ht, ← hg]
  exact hom_apply_hom_apply_of_comp_eq (tateGlobalToLocal_tateLocalToCompact (gsFinFamily S ιs)
    (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs) realUnits
    (realUnitsMor S ιr) m) g

include h2S in

theorem eq_zero_unitsTateCohomology_of_two_pow_nsmul {r : ℕ} (hr : 4 ≤ r) (x : unitsTateCohomology S ιr ιs r)
    {k : ℕ} (hk : 2 ^ k • x = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 + 1 := ⟨r - 2, by omega⟩
  exact eq_zero_of_tateToGlobal_units_eq_zero S ιr ιs h2S (by omega) x
    (tateToGlobal_units_eq_zero S ιr ιs h2S (by omega) x hk)

end Real

end

end GroundTheory.ProfCoh
