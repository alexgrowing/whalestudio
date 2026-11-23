import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
import GroundTheory.ProfiniteCohomology.CupProducts.Projection
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (ℓ : ℕ) [NeZero ℓ] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

def gsRootsLocalUnitsMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S ℓ) ⟶
      galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  gsRootsOmegaMor S ιs ℓ v ≫
    (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ℓ).f

theorem gsRootsLocalUnitsMor_eq (v : S) :
    gsRootsLocalUnitsMor S ιs ℓ v =
      (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) ≫ gsSUnitsLocalMor S ιs v :=
  (gsKummerLocalMap S ιs ℓ v).comm₁₂.symm

include hℓS in

theorem cohomologyMap_gsRootsLocalUnitsMor_injective (v : S) :
    Function.Injective (cohomologyMap (gsRootsLocalUnitsMor S ιs ℓ v) 2).hom := by
  have h2 := cohomologyMap_f_injective_of_subsingleton (localKummer_shortExact S ℓ v) 1
    subsingleton_cohomology_one_galUnits
  have h1 : Function.Injective (cohomologyMap (gsRootsOmegaMor S ιs ℓ v) 2).hom := by
    have hc := congrArg (fun φ => cohomologyMap φ 2)
      (comp_repInvOfBijective (gsRootsOmegaMor S ιs ℓ v) (bijective_gsRootsOmegaMor S ιs ℓ hℓS v))
    have hc' := (cohomologyMap_comp _ _ 2).symm.trans (hc.trans (cohomologyMap_id 2))
    refine Function.LeftInverse.injective (g := (cohomologyMap (repInvOfBijective
      (gsRootsOmegaMor S ιs ℓ v) (bijective_gsRootsOmegaMor S ιs ℓ hℓS v)) 2).hom) fun a => ?_
    exact congrArg (fun φ => φ.hom a) hc'
  have e := cohomologyMap_comp (gsRootsOmegaMor S ιs ℓ v)
    (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ℓ).f 2
  intro a b hab
  have hab' := (congrArg (fun φ => φ.hom a) e).symm.trans ((hab : _).trans (congrArg (fun φ => φ.hom b) e))
  exact h1 (h2 hab')

include hℓS in

theorem ptRes_eq_zero_iff (v : S) (x : cohomology (gsRoots S ℓ) 2) :
    ptRes (gsFinFamily S ιs) (gsRoots S ℓ) v 2 x = 0 ↔
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) = 0 := by
  have e1 := cohomologyMap_cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
    (continuous_toMonoidHom _) (𝟙 _) (gsRootsLocalUnitsMor S ιs ℓ v) (p := 2) x
  have e2 := cohomologyMapAlong_cohomologyMap (gsFinFamily S ιs v).toMonoidHom
    (continuous_toMonoidHom _) (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)
    (gsSUnitsLocalMor S ιs v) (p := 2) x
  have e3 := congrArg (fun m => (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
    (continuous_toMonoidHom _) m 2).hom x)
    ((Category.id_comp (gsRootsLocalUnitsMor S ιs ℓ v)).trans (gsRootsLocalUnitsMor_eq S ιs ℓ v))
  have key : (cohomologyMap (gsRootsLocalUnitsMor S ιs ℓ v) 2).hom
      (ptRes (gsFinFamily S ιs) (gsRoots S ℓ) v 2 x) =
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) :=
    e1.trans (e3.trans e2.symm)
  constructor
  · intro h
    exact key.symm.trans ((congrArg (cohomologyMap (gsRootsLocalUnitsMor S ιs ℓ v) 2).hom h).trans
      (map_zero _))
  · intro h
    exact cohomologyMap_gsRootsLocalUnitsMor_injective S ιs ℓ hℓS v ((key.trans h).trans (map_zero _).symm)

variable {ℓ} (hℓ : ℓ.Prime)

set_option maxHeartbeats 4000000 in
omit [NeZero ℓ] in
include hℓS hℓ in

theorem eq_zero_of_gsSUnitsLocalMor_eq_zero (hK : Odd ℓ ∨ IsTotallyComplex K.1)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) (hy : ℓ • y = 0)
    (hloc : ∀ v : S, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (gsSUnitsLocalMor S ιs v) 2).hom y = 0) : y = 0 := by
  classical
  have hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := fun v hv => by
    by_contra h
    exact hℓS v h hv
  have hy1 : ℓ ^ 1 • y = 0 := by rw [pow_one]; exact hy
  refine eq_zero_of_sUnitsBrauer_eq_zero K S ℓ hℓ hS y 1 hy1 ?_
  refine eq_zero_of_brauerLocal_apply_eq_zero (gsLocalEmbeddings S ιs) _ fun w => ?_
  rcases w with w | w
  · apply placeInv_injective (K := K) (.inl w)
    refine (placeInv_inl_eq_zero (ℓ ^ 1) (hK.imp (fun h => h.pow) id) w _ ?_).trans (map_zero _).symm
    have e : ℓ ^ 1 • brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) = 0 := by
      rw [← map_nsmul, ← map_nsmul, hy1, map_zero, map_zero]
    exact (map_nsmul (DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w)
      (Sum.inl w : Place K.1)) (ℓ ^ 1) _).symm.trans
      ((congrArg (DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w)
        (Sum.inl w : Place K.1)) e).trans (map_zero _))
  · by_cases hw : w ∈ S
    · refine (congrArg (fun z => brauerLocal (gsLocalEmbeddings S ιs) z (.inr w))
        (sUnitsBrauer_apply K S _)).trans ?_
      refine (brauerLocal_gsBrauerInfl_inr K S (gsLocalEmbeddings S ιs) w _).trans ?_
      have hfin : (gsLocalEmbeddings S ιs).fin w = ιs ⟨w, hw⟩ := gsLocalEmbeddings_fin S ιs ⟨w, hw⟩
      rw [hfin]
      refine (gsLocalRes_sUnitsToUnits_eq S ιs ⟨w, hw⟩ _).trans ?_
      rw [hloc ⟨w, hw⟩, map_zero, map_zero]
      rfl
    · exact brauerLocal_sUnitsBrauer_inr K S _ _ w hw

include hℓS hℓ in

theorem mem_ptSha_iff_cohomologyMap_eq_zero (hK : Odd ℓ ∨ IsTotallyComplex K.1)
    (x : cohomology (gsRoots S ℓ) 2) :
    x ∈ ptSha (gsFinFamily S ιs) (gsRoots S ℓ) 2 ↔
      (cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x = 0 := by
  rw [mem_ptSha]
  constructor
  · intro hx
    have hloc : ∀ v : S, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) = 0 :=
      fun v => (ptRes_eq_zero_iff S ιs ℓ hℓS v x).1 (congrFun hx v)
    have h0 : (cohomologyMap (ℓ • 𝟙 (galSUnitsMax K.1 ℚ̄ S)) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) = 0 :=
      cohomologyMap_g_cohomologyMap_f_apply
        (S := sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2 x
    exact eq_zero_of_gsSUnitsLocalMor_eq_zero S ιs hℓS hℓ hK _
      ((cohomologyMap_nsmul_id_apply (galSUnitsMax K.1 ℚ̄ S) ℓ 2 _).symm.trans h0) hloc
  · intro hy
    funext v
    exact (ptRes_eq_zero_iff S ιs ℓ hℓS v x).2 ((congrArg _ hy).trans (map_zero _))

include hℓS hℓ in

theorem mem_ptSha_iff_exists_δ (hK : Odd ℓ ∨ IsTotallyComplex K.1) (x : cohomology (gsRoots S ℓ) 2) :
    x ∈ ptSha (gsFinFamily S ιs) (gsRoots S ℓ) 2 ↔
      ∃ z : cohomology (galSUnitsMax K.1 ℚ̄ S) 1,
        (δ (sUnitsKummerSequence_shortExact (Ω := ℚ̄) S ℓ hℓS) 1 2 rfl).hom z = x := by
  refine (mem_ptSha_iff_cohomologyMap_eq_zero S ιs hℓS hℓ hK x).trans ⟨fun h => ?_, ?_⟩
  · exact exists_δ_eq_of_cohomologyMap_f_eq_zero (sUnitsKummerSequence_shortExact (Ω := ℚ̄) S ℓ hℓS) 1 2 rfl x h
  · rintro ⟨z, rfl⟩
    exact congrArg (fun φ => φ.hom z) (δ_comp (sUnitsKummerSequence_shortExact (Ω := ℚ̄) S ℓ hℓS) 1 2 rfl)

end

end GroundTheory.ProfCoh
