import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerSha
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerSeq
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseTransportGS
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance 2000] Rep.hV2

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))}
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

set_option maxHeartbeats 800000 in

theorem ptCompactToGlobal_gsMackeyCompactIso (ℓ : ℕ)
    (c : compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) :
    (ptCompactToGlobal (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2).hom
        ((gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).hom.hom c) =
      (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom
        ((ptCompactToGlobal (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
          (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2).hom c) := by
  have hT := compactTransport_compactToGlobal (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) (gsBaseChange S hL) (mackeyPlaceEquiv S hL ιs)
    (fun p => gsMackeyLocalEquiv hL ιs p.1 p.2.out) (gsBaseChange_mackeyFamily_eq hL ιs)
    (gsRootsOfUnityIso S hL ℓ).symm.hom 2
  have hG : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom =
      cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsRootsOfUnityIso S hL ℓ).symm.hom 2 :=
    cohomologyIsoOfContinuousMulEquiv_hom _ _ 2
  have hC : (gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).hom =
      compactTransport (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) (gsBaseChange S hL) (mackeyPlaceEquiv S hL ιs)
        (fun p => gsMackeyLocalEquiv hL ιs p.1 p.2.out) (gsBaseChange_mackeyFamily_eq hL ιs)
        (gsRootsOfUnityIso S hL ℓ).symm.hom 2 :=
    gsMackeyCompactIso_hom hL ιs _ 2
  have s1 := congrArg (fun ψ => (ptCompactToGlobal (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2).hom (ψ.hom c)) hC
  have s3 := congrArg (fun ψ => ψ.hom ((ptCompactToGlobal (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2).hom c)) hG
  have s2 := congrArg (fun φ => φ.hom c) hT
  exact s1.trans (s2.trans s3.symm)

set_option maxHeartbeats 800000 in

theorem mem_ptSha_mackey_iff (ℓ : ℕ)
    (x : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) :
    (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x ∈
        ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
          (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2 ↔
      x ∈ ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2 := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := exists_ptCompactToGlobal_eq_of_mem_ptSha
      (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs)) (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) hx
    obtain ⟨c', hc'⟩ := (gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).toLinearEquiv.surjective c
    have h1 := (ptCompactToGlobal_gsMackeyCompactIso hL ιs ℓ c').symm.trans
      ((congrArg (ptCompactToGlobal (mackeyFamily (gsOpenSubgroup S hL)
        (gsFinFamily S ιs)) (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2).hom hc').trans hc)
    have h2 := (gsRootsOfUnityCohomologyIso S hL ℓ 2).toLinearEquiv.injective h1
    exact (congrArg (· ∈ ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) h2).mp
      (ptCompactToGlobal_mem_ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) c')
  · intro hx
    have hc := exists_ptCompactToGlobal_eq_of_mem_ptSha _ _ hx
    obtain ⟨c', hc'⟩ := hc
    have h1 := (ptCompactToGlobal_gsMackeyCompactIso hL ιs ℓ c').trans
      (congrArg (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom hc')
    exact (congrArg (· ∈ ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2) h1).mp
      (ptCompactToGlobal_mem_ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (Rep.res (gsSubtype S hL) (gsRoots S ℓ))
        ((gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).hom.hom c'))

theorem gsRootsOfUnityIso_symm_comp_rootsOfUnityToSUnits (ℓ : ℕ) [NeZero ℓ] :
    (gsRootsOfUnityIso S hL ℓ).symm.hom ≫ (Rep.resFunctor (gsSubtype S hL)).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) =
      (Rep.resFunctor (gsBaseChange S hL).toMulEquiv.toMonoidHom).map
        (rootsOfUnityToSUnits (placesOver S) (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) ≫
        (gsSUnitsIso S hL).symm.hom :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

set_option maxHeartbeats 800000 in

theorem cohomologyMap_rootsOfUnityToSUnits_gsRootsOfUnityCohomologyIso (ℓ : ℕ) [NeZero ℓ]
    (x : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) :
    (cohomologyMap ((Rep.resFunctor (gsSubtype S hL)).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 2).hom
        ((gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x) =
      (gsSUnitsCohomologyIso S hL 2).hom.hom
        ((cohomologyMap (rootsOfUnityToSUnits (placesOver S)
          (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) 2).hom x) := by
  have hG : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom =
      cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsRootsOfUnityIso S hL ℓ).symm.hom 2 :=
    cohomologyIsoOfContinuousMulEquiv_hom _ _ 2
  have hO : (gsSUnitsCohomologyIso S hL 2).hom =
      cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsSUnitsIso S hL).symm.hom 2 :=
    cohomologyIsoOfContinuousMulEquiv_hom _ _ 2
  have s1 := congrArg (fun ψ => (cohomologyMap ((Rep.resFunctor (gsSubtype S hL)).map
    (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 2).hom (ψ.hom x)) hG
  have s4 := congrArg (fun ψ => ψ.hom ((cohomologyMap (rootsOfUnityToSUnits (placesOver S)
    (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) 2).hom x)) hO
  have s2 := cohomologyMap_cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsRootsOfUnityIso S hL ℓ).symm.hom
    ((Rep.resFunctor (gsSubtype S hL)).map (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ))
    (p := 2) x
  have s3 := cohomologyMapAlong_cohomologyMap (gsBaseChange S hL).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL))
    (rootsOfUnityToSUnits (placesOver S) (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ)
    (gsSUnitsIso S hL).symm.hom (p := 2) x
  have s5 := congrArg (fun m => (cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) m 2).hom x)
    (gsRootsOfUnityIso_symm_comp_rootsOfUnityToSUnits hL ℓ)
  exact s1.trans (s2.trans (s5.trans (s3.symm.trans s4.symm)))

theorem gsRootsOfUnityCohomologyIso_hom_inv_apply (ℓ : ℕ)
    (x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2) :
    (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom ((gsRootsOfUnityCohomologyIso S hL ℓ 2).inv.hom x) = x :=
  congrArg (fun φ => φ.hom x) (gsRootsOfUnityCohomologyIso S hL ℓ 2).inv_hom_id

set_option maxHeartbeats 800000 in

theorem mem_ptSha_mackey_iff_of_eq (ℓ : ℕ)
    {x' : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2}
    {x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2}
    (hx : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x' = x) :
    x ∈ ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2 ↔
      x' ∈ ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2 := by
  subst hx
  exact mem_ptSha_mackey_iff hL ιs ℓ x'

set_option maxHeartbeats 800000 in

theorem cohomologyMap_rootsOfUnityToSUnits_eq_zero_iff_of_eq (ℓ : ℕ) [NeZero ℓ]
    {x' : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2}
    {x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2}
    (hx : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x' = x) :
    (cohomologyMap (rootsOfUnityToSUnits (placesOver S)
      (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) 2).hom x' = 0 ↔
      (cohomologyMap ((Rep.resFunctor (gsSubtype S hL)).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 2).hom x = 0 := by
  subst hx
  rw [cohomologyMap_rootsOfUnityToSUnits_gsRootsOfUnityCohomologyIso hL ℓ x']
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    exact (gsSUnitsCohomologyIso S hL 2).toLinearEquiv.injective (h0.trans (map_zero _).symm)

set_option maxHeartbeats 1600000 in

theorem mem_ptSha_mackey_iff_exists_kummerModN {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (hK : Odd ℓ ∨ IsTotallyComplex L.1)
    (x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2) :
    x ∈ ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2 ↔
      ∃ y, kummerModNHom (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsKummer_shortExact S ℓ hℓS) 1 y = x := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := fun v hv => by
    by_contra h
    exact hℓS v h hv
  have hℓS' : ∀ w ∉ (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))), ((ℓ : ℕ) : 𝓞 L.1) ∉ w.asIdeal :=
    natCast_not_mem_of_not_mem_placesOver hn
  have hx' := gsRootsOfUnityCohomologyIso_hom_inv_apply hL ℓ x
  refine (mem_ptSha_mackey_iff_of_eq hL ιs ℓ hx').trans
    ((mem_ptSha_iff_cohomologyMap_eq_zero (K := L) (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))
      (gsMackeyEmbeddings hL ιs) hℓS' hℓ hK ((gsRootsOfUnityCohomologyIso S hL ℓ 2).inv.hom x)).trans
    ((cohomologyMap_rootsOfUnityToSUnits_eq_zero_iff_of_eq hL ℓ hx').trans
    (Iff.trans ?_ (kummerTorsHom_eq_zero_iff (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsKummer_shortExact S ℓ hℓS) 1 x))))
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end

end GroundTheory.ProfCoh
