import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingUnitsDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Kummer

abbrev finKummer (v : S) :=
  localKummerSeq S (gsFinFamily S ιs v).toMonoidHom
    ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιs v))

abbrev realKummer (w : {v : InfinitePlace K.1 // v.IsReal}) :=
  localKummerSeq S (gsRealFamily S ιr w).toMonoidHom
    ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιr w))

abbrev finKummerMap (v : S) :=
  kummerLocalMap S (gsFinFamily S ιs v).toMonoidHom
    ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιs v))

abbrev realKummerMap (w : {v : InfinitePlace K.1 // v.IsReal}) :=
  kummerLocalMap S (gsRealFamily S ιr w).toMonoidHom
    ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιr w))

instance (v : S) : IsDiscreteRep (finKummer S ιs v).X₁ :=
  IsDiscreteRep.res (continuous_toMonoidHom (gsFinFamily S ιs v)) _

instance (v : S) : IsDiscreteRep (finKummer S ιs v).X₂ := isDiscreteRep_finUnits S v

instance (v : S) : IsDiscreteRep (finKummer S ιs v).X₃ := isDiscreteRep_finUnits S v

instance (w : {v : InfinitePlace K.1 // v.IsReal}) : IsDiscreteRep (realKummer S ιr w).X₁ :=
  IsDiscreteRep.res (continuous_toMonoidHom (gsRealFamily S ιr w)) _

instance (w : {v : InfinitePlace K.1 // v.IsReal}) : IsDiscreteRep (realKummer S ιr w).X₂ :=
  isDiscreteRep_realUnits w

instance (w : {v : InfinitePlace K.1 // v.IsReal}) : IsDiscreteRep (realKummer S ιr w).X₃ :=
  isDiscreteRep_realUnits w

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include h2S in

theorem kummerSeq_shortExact :
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2).ShortExact :=
  sUnitsKummerSequence_shortExact (Ω := ℚ̄) S 2 (fun v hv h => hv (h2S v h))

def kummerF (n : ℕ) :
    gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) n →+
      unitsTateCohomology S ιr ιs n :=
  (tateCompactCohomologyMap₁₂ (gsFinFamily S ιs) (gsRealFamily S ιr)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2) (finKummer S ιs) (finKummerMap S ιs)
    (realKummer S ιr) (realKummerMap S ιr) n).hom.toAddMonoidHom

def kummerG (n : ℕ) : unitsTateCohomology S ιr ιs n →+ unitsTateCohomology S ιr ιs n :=
  (tateCompactCohomologyMap₂₃ (gsFinFamily S ιs) (gsRealFamily S ιr)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2) (finKummer S ιs) (finKummerMap S ιs)
    (realKummer S ιr) (realKummerMap S ιr) n).hom.toAddMonoidHom

def kummerδ (n : ℕ) : unitsTateCohomology S ιr ιs n →+
    gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) (n + 1) :=
  (tateCompactδ (gsFinFamily S ιs) (gsRealFamily S ιr) (finKummerMap S ιs) (realKummerMap S ιr)
    (kummerSeq_shortExact S h2S) (fun _ => localKummerSeq_shortExact _ _ _ _)
    (fun _ => localKummerSeq_shortExact _ _ _ _) n).hom.toAddMonoidHom

set_option maxHeartbeats 1000000 in

theorem kummerG_apply (n : ℕ) (y : unitsTateCohomology S ιr ιs n) : kummerG S ιr ιs n y = 2 • y := by
  have h : tateCompactCohomologyMap₂₃ (gsFinFamily S ιs) (gsRealFamily S ιr)
      (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2) (finKummer S ιs) (finKummerMap S ιs)
      (realKummer S ιr) (realKummerMap S ιr) n = 2 • 𝟙 _ :=
    tateCompactCohomologyMap_nsmul_id (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S)
      (finUnits S) (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) 2 n _ _
  exact congrArg (fun f => f.hom y) h

set_option maxHeartbeats 1000000 in

theorem kummerG_kummerF (n : ℕ)
    (x : gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) n) :
    kummerG S ιr ιs n (kummerF S ιr ιs n x) = 0 :=
  hom_apply_hom_apply_of_comp_eq (tateCompactCohomologyMap_f_g (gsFinFamily S ιs) (gsRealFamily S ιr)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2) (finKummer S ιs) (finKummerMap S ιs)
    (realKummer S ιr) (realKummerMap S ιr) n) x

set_option maxHeartbeats 1000000 in

theorem exists_kummerδ_eq (n : ℕ)
    (x : gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) (n + 1))
    (hx : kummerF S ιr ιs (n + 1) x = 0) : ∃ y, kummerδ S ιr ιs h2S n y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (tateCompactCohomology_exact₁ (gsFinFamily S ιs) (gsRealFamily S ιr)
    (finKummerMap S ιs) (realKummerMap S ιr) (kummerSeq_shortExact S h2S)
    (fun _ => localKummerSeq_shortExact _ _ _ _) (fun _ => localKummerSeq_shortExact _ _ _ _) n) x hx

set_option maxHeartbeats 1000000 in

theorem kummerδ_kummerG (n : ℕ) (y : unitsTateCohomology S ιr ιs n) :
    kummerδ S ιr ιs h2S n (kummerG S ιr ιs n y) = 0 :=
  hom_apply_hom_apply_of_comp_eq (tateCompactCohomologyMap₂₃_tateCompactδ (gsFinFamily S ιs)
    (gsRealFamily S ιr) (finKummerMap S ιs) (realKummerMap S ιr) (kummerSeq_shortExact S h2S)
    (fun _ => localKummerSeq_shortExact _ _ _ _) (fun _ => localKummerSeq_shortExact _ _ _ _) n) y

end Kummer

section Main

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include h2S in

theorem gsTateCompactCohomology_rootsOfUnity_two_eq_zero {r : ℕ} (hr : 4 ≤ r)
    (x : gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) r) :
    x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hf : kummerF S ιr ιs (n + 1) x = 0 := by
    refine eq_zero_unitsTateCohomology_of_two_pow_nsmul S ιr ιs h2S hr _ (k := 1) ?_
    rw [pow_one, ← kummerG_apply]
    exact kummerG_kummerF S ιr ιs (n + 1) x
  obtain ⟨y, rfl⟩ := exists_kummerδ_eq S ιr ιs h2S n x hf
  obtain ⟨y', rfl⟩ := exists_two_nsmul_unitsTateCohomology S ιr ιs h2S (by omega) y
  rw [← kummerG_apply]
  exact kummerδ_kummerG S ιr ιs h2S n y'

end Main

section ZModTwo

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

instance isDiscreteRep_zmodRep_two_gs : IsDiscreteRep (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) :=
  isDiscreteRep_of_isTrivial _

theorem galRootsOfUnity_two_ρ_apply (σ : galUnramifiedOutside K.1 ℚ̄ S)
    (x : Additive (rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S))) :
    (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2).ρ σ x = x := by
  rw [galRootsOfUnity_ρ_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change σ (((Additive.toMul x : rootsOfUnity 2 _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    maxUnramifiedOutside K.1 ℚ̄ S) = (((Additive.toMul x : rootsOfUnity 2 _) :
      (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)
  have hx : (((Additive.toMul x : rootsOfUnity 2 _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
      maxUnramifiedOutside K.1 ℚ̄ S) * (((Additive.toMul x : rootsOfUnity 2 _) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) = 1 := by
    rw [← Units.val_mul, ← pow_two, (mem_rootsOfUnity 2 _).1 (Additive.toMul x).2, Units.val_one]
  rcases mul_self_eq_one_iff.1 hx with h | h <;> rw [h]
  · exact map_one σ
  · rw [map_neg, map_one]

include h2S in

theorem nonempty_rootsOfUnity_two_iso_zmodRep :
    Nonempty (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2 ≅
      zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) := by
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity_gs K S Nat.prime_two h2S
  exact ⟨Rep.mkIso (Representation.Equiv.mk (uliftIntLinearEquiv.{0} (e.symm.trans AddEquiv.ulift.symm))
    fun σ => LinearMap.ext fun x => by
      change (uliftIntLinearEquiv.{0} (e.symm.trans AddEquiv.ulift.symm))
        ((galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2).ρ σ x) =
          (uliftIntLinearEquiv.{0} (e.symm.trans AddEquiv.ulift.symm)) x
      rw [galRootsOfUnity_two_ρ_apply])⟩

include h2S in

theorem gsTateCompactCohomology_zmodRep_two_eq_zero {r : ℕ} (hr : 4 ≤ r)
    (x : gsTateCompactCohomology S ιr ιs (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) r) : x = 0 := by
  obtain ⟨e⟩ := nonempty_rootsOfUnity_two_iso_zmodRep S h2S
  exact eq_zero_tateCompactCohomologyRes_of_retract (gsFinFamily S ιs) (gsRealFamily S ιr) e.inv e.hom
    e.inv_hom_id r (gsTateCompactCohomology_rootsOfUnity_two_eq_zero S ιr ιs h2S hr) x

instance isDiscreteRep_res_zmodRep_two_fin (v : S) :
    IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) :=
  isDiscreteRep_res_toMonoidHom _ _

theorem subsingleton_finLocal_zmodRep_two (v : S) {n : ℕ} (hn : 3 ≤ n) :
    Subsingleton (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) n) := by
  refine subsingleton_cohomology_of_cdp_le_two two_ne_zero (fun ℓ hℓ _ => ?_) _
    (fun m => nsmul_zmodRep_eq_zero _ 2 m) hn
  refine cdp_galois_le_two _ _ hℓ ?_
  exact_mod_cast hℓ.ne_zero

def someFinEmbeddings : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) :=
  fun _ => Classical.choice nonempty_algHom_of_isSepClosed

set_option maxHeartbeats 1000000 in
include h2S in

theorem injective_gsRealRes_zmodRep_two_succ {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (gsRealRes S ιr (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) (n + 1)).hom :=
  (injective_tateGlobalToLocal_iff (gsFinFamily S (someFinEmbeddings S)) (gsRealFamily S ιr)
    (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)
    (fun v => Rep.res (gsFinFamily S (someFinEmbeddings S) v).toMonoidHom
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2))
    (fun _ => 𝟙 _) (n + 1)
    (fun v => subsingleton_finLocal_zmodRep_two S (someFinEmbeddings S) v (by omega))).1
    (injective_tateGlobalToLocal_of_eq_zero (gsFinFamily S (someFinEmbeddings S)) (gsRealFamily S ιr)
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)
      (fun v => Rep.res (gsFinFamily S (someFinEmbeddings S) v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2))
      (fun _ => 𝟙 _) n
      (gsTateCompactCohomology_zmodRep_two_eq_zero S ιr (someFinEmbeddings S) h2S (by omega)))

set_option maxHeartbeats 1000000 in
include h2S in

theorem surjective_gsRealRes_zmodRep_two_succ {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective (gsRealRes S ιr (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) (n + 1)).hom :=
  (surjective_tateGlobalToLocal_iff (gsFinFamily S (someFinEmbeddings S)) (gsRealFamily S ιr)
    (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)
    (fun v => Rep.res (gsFinFamily S (someFinEmbeddings S) v).toMonoidHom
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2))
    (fun _ => 𝟙 _) (n + 1)
    (fun v => subsingleton_finLocal_zmodRep_two S (someFinEmbeddings S) v (by omega))).1
    (surjective_tateGlobalToLocal_of_eq_zero (gsFinFamily S (someFinEmbeddings S)) (gsRealFamily S ιr)
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)
      (fun v => Rep.res (gsFinFamily S (someFinEmbeddings S) v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2))
      (fun _ => 𝟙 _) n
      (gsTateCompactCohomology_zmodRep_two_eq_zero S ιr (someFinEmbeddings S) h2S (by omega)))

set_option maxHeartbeats 4000000 in
include h2S in

theorem injective_gsRealRes_zmodRep_two {r : ℕ} (hr : 4 ≤ r) :
    Function.Injective (gsRealRes S ιr (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) r).hom := by
  cases r with
  | zero => omega
  | succ n => exact injective_gsRealRes_zmodRep_two_succ S ιr h2S (by omega)

set_option maxHeartbeats 4000000 in
include h2S in

theorem surjective_gsRealRes_zmodRep_two {r : ℕ} (hr : 3 ≤ r) :
    Function.Surjective (gsRealRes S ιr (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) r).hom := by
  cases r with
  | zero => omega
  | succ n => exact surjective_gsRealRes_zmodRep_two_succ S ιr h2S (by omega)

end ZModTwo

end

end GroundTheory.ProfCoh
