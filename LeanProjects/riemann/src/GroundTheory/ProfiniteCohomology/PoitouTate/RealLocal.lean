import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealAbstract
import GroundTheory.ProfiniteCohomology.PoitouTate.BrauerInvZOfIsSepClosureCohomologyULiftIntAddEqu
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityPlace
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

section NormClassMap

variable {k F : Type} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [Fintype F]

theorem cohomologyMap_normClass {B B' : Rep k F} [IsDiscreteRep B] [IsDiscreteRep B'] (f : B ⟶ B')
    (m : B) : (cohomologyMap f 0).hom (normClass B m) = normClass B' (f.hom m) := by
  obtain ⟨z, hz, hiz⟩ := exists_normClass_cycle B m
  obtain ⟨z', hz', hiz'⟩ := exists_normClass_cycle B' (f.hom m)
  rw [hz, hz']
  change (HomologicalComplex.homologyMap (cochainsMap f) 0).hom _ = _
  rw [homologyMap_homologyπ_apply]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, hiz, hiz']
  apply cochainOf_injective
  funext σ
  change f.hom ((∑ g, B.ρ g) m) = (∑ g, B'.ρ g) (f.hom m)
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => Rep.hom_comm_apply f g m

end NormClassMap

section Abstract

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ψ : Gal(L/K) →ₜ* G)
  (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (ρ : Rep.res ψ.toMonoidHom D ⟶ galUnits.{0} K L)
  (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]

abbrev resEvalPair :
    Rep.res ψ.toMonoidHom M ⊗ Rep.res ψ.toMonoidHom (dualRep D M) ⟶ Rep.res ψ.toMonoidHom D :=
  (Rep.resFunctor ψ.toMonoidHom).map (evalPairing D M)

def dualToCartier :
    Rep.res ψ.toMonoidHom (dualRep D M) ⟶ cartierDual K L (Rep.res ψ.toMonoidHom M) :=
  resDualPost ψ.toMonoidHom D M _ ρ

omit [IsTopologicalGroup G] [IsDiscreteRep D] [IsDiscreteRep M] in
theorem bijective_dualToCartier {n : ℕ} [NeZero n] (hL : Nonempty (galRootsOfUnity.{0} K L n ≃+ ZMod n))
    (hD : Nonempty (D ≃+ ZMod n)) (hρ : Function.Injective ρ.hom) [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (dualToCartier ψ D ρ M).hom := by
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (galRootsOfUnity.{0} K L n) := finite_of_nonempty_addEquiv hL
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  have : Finite (Rep.res ψ.toMonoidHom M) := inferInstanceAs (Finite M)
  have : Finite (dualRep (galRootsOfUnity.{0} K L n) (Rep.res ψ.toMonoidHom M)) := finite_dualRep
  set e := dualRepRootsOfUnityIso K L (Rep.res ψ.toMonoidHom M) n hM
  have he : Function.Injective e.inv.hom := fun a b hab => by
    have h := congrArg e.hom.hom hab
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, e.inv_hom_id] at h
  have : Finite (cartierDual K L (Rep.res ψ.toMonoidHom M)) := Finite.of_injective _ he
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro f f' hff'
    exact LinearMap.ext fun m => hρ (LinearMap.congr_fun hff' m)
  · calc _ ≤ Nat.card (dualRep (galRootsOfUnity.{0} K L n) (Rep.res ψ.toMonoidHom M)) :=
          Nat.card_le_card_of_injective _ he
      _ ≤ Nat.card M := card_dualRep_le hL
      _ ≤ Nat.card (dualRep D (dualRep D M)) :=
          Nat.card_le_card_of_injective _ (bijective_toDualDual hD hM).1
      _ ≤ Nat.card (dualRep D M) := card_dualRep_le hD

omit [IsTopologicalGroup G] [IsDiscreteRep D] [IsDiscreteRep M] in

theorem tensorHom_dualToCartier_cartierPairing :
    (𝟙 (Rep.res ψ.toMonoidHom M) ⊗ₘ dualToCartier ψ D ρ M) ≫
        cartierPairing K L (Rep.res ψ.toMonoidHom M) =
      resEvalPair ψ D M ≫ ρ := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cupPairing_dualToCartier [Finite M] [IsDiscreteRep (galUnits.{0} K L)]
    [IsDiscreteRep (cartierDual K L (Rep.res ψ.toMonoidHom M))] {r s : ℕ} (h : r + s = 2)
    (ξ : cohomology (Rep.res ψ.toMonoidHom M) r)
    (η : cohomology (Rep.res ψ.toMonoidHom (dualRep D M)) s) :
    cupPairing (cartierPairing K L (Rep.res ψ.toMonoidHom M)) h ξ
        ((cohomologyMap (dualToCartier ψ D ρ M) s).hom η) =
      (cohomologyMap ρ 2).hom (cupPairing (resEvalPair ψ D M) h ξ η) := by
  have hc := cupPairing_cohomologyMap (cartierPairing K L (Rep.res ψ.toMonoidHom M))
    (𝟙 _) (dualToCartier ψ D ρ M) h ξ η
  rw [cohomologyMap_id, ModuleCat.id_apply] at hc
  rw [hc, tensorHom_dualToCartier_cartierPairing, cohomologyMap_cupPairing]

section Order2

variable [FiniteDimensional K L] [IsGalois K L] (h2 : Module.finrank K L ≤ 2)
  (hN : ∀ a b : Kˣ, (a : K) ∉ Set.range (Algebra.norm K : L → K) →
    (b : K) ∉ Set.range (Algebra.norm K : L → K) →
      ((a * b : Kˣ) : K) ∈ Set.range (Algebra.norm K : L → K))
  {c : Gal(L/K)} (hG : ∀ g : Gal(L/K), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : K) ∉ Set.range (Algebra.norm K : L → K))
  (hconj : ∀ ζ : galUnits.{0} K L, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (galUnits.{0} K L).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (galRootsOfUnity.{0} K L k ≃+ ZMod k))
  [IsDiscreteRep (galUnits.{0} K L)] [Finite M]
  [IsDiscreteRep (cartierDual K L (Rep.res ψ.toMonoidHom M))]
  (inv : cohomology (Rep.res ψ.toMonoidHom D) 2 →+ QZ)
  (hinv : ∀ z, inv z = realInv K L h2 hN ((cohomologyMap ρ 2).hom z))

include hG hc hneg hconj hroots hinv in

theorem exists_orderTwo_pairing_zero {n : ℕ} [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    (hρ : Function.Injective ρ.hom) (hM : ∀ m : M, n • m = 0)
    (χ : cohomology (Rep.res ψ.toMonoidHom (dualRep D M)) 2 →+ QZ) :
    ∃ ξ : cohomology (Rep.res ψ.toMonoidHom M) 0, ∀ η,
      inv (cupPairing (resEvalPair ψ D M) (show 0 + 2 = 2 from rfl) ξ η) = χ η := by
  have hf := bijective_dualToCartier ψ D ρ M (hroots n (Nat.pos_of_ne_zero (NeZero.ne n))) hD hρ hM
  let e := cohomologyAddEquivOfIso (Rep.isoOfBijective _ hf) 2
  obtain ⟨x, hx⟩ := (real_local_duality_of_orderTwo h2 hN hG hc hneg hconj hroots
    (Rep.res ψ.toMonoidHom M)).1.1.2 (χ.comp e.symm.toAddMonoidHom)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨x, fun η => ?_⟩
  have e1 := DFunLike.congr_fun hx (e η)
  rw [realDualityPairingZeroTwo_mk, realDualityPairing_apply] at e1
  rw [hinv, ← cupPairing_dualToCartier]
  refine e1.trans ?_
  change χ (e.symm (e η)) = χ η
  rw [AddEquiv.symm_apply_apply]

include hG hc hneg hconj hroots hinv in

theorem exists_orderTwo_pairing_two {n : ℕ} [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    (hρ : Function.Injective ρ.hom) (hM : ∀ m : M, n • m = 0)
    (χ : cohomology (Rep.res ψ.toMonoidHom (dualRep D M)) 0 →+ QZ)
    (hχ : ∀ x ∈ normClasses (Rep.res ψ.toMonoidHom (dualRep D M)), χ x = 0) :
    ∃ ξ : cohomology (Rep.res ψ.toMonoidHom M) 2, ∀ η,
      inv (cupPairing (resEvalPair ψ D M) (show 2 + 0 = 2 from rfl) ξ η) = χ η := by
  set f := dualToCartier ψ D ρ M
  have hf := bijective_dualToCartier ψ D ρ M (hroots n (Nat.pos_of_ne_zero (NeZero.ne n))) hD hρ hM
  let e := cohomologyAddEquivOfIso (Rep.isoOfBijective f hf) 0
  let χ' := χ.comp e.symm.toAddMonoidHom
  have hχ' : ∀ y ∈ normClasses (cartierDual K L (Rep.res ψ.toMonoidHom M)), χ' y = 0 := fun y hy => by
    obtain ⟨m', rfl⟩ := exists_normClass_eq_of_mem _ y hy
    obtain ⟨m, rfl⟩ := hf.2 m'
    have hem : e (normClass _ m) = normClass _ (f.hom m) := by
      rw [cohomologyAddEquivOfIso_apply]
      exact cohomologyMap_normClass f m
    rw [← hem]
    change χ (e.symm (e (normClass _ m))) = 0
    rw [AddEquiv.symm_apply_apply]
    exact hχ _ (normClass_mem_normClasses _ m)
  obtain ⟨ξ, hξ⟩ := (real_local_duality_of_orderTwo h2 hN hG hc hneg hconj hroots
    (Rep.res ψ.toMonoidHom M)).2.2.1.2 (QuotientAddGroup.lift _ χ' hχ')
  refine ⟨ξ, fun η => ?_⟩
  have e1 := DFunLike.congr_fun hξ (Submodule.Quotient.mk (e η))
  rw [realDualityPairingTwoZero_mk, realDualityPairing_apply] at e1
  rw [hinv, ← cupPairing_dualToCartier]
  refine e1.trans ?_
  change χ (e.symm (e η)) = χ η
  rw [AddEquiv.symm_apply_apply]

end Order2

end Abstract

section GS

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (n : ℕ)

def gsRealRootsToUnits (w : {v : InfinitePlace K.1 // v.IsReal}) :
    Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S n) ⟶
      galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion) :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)))
      (B := Additive (AlgebraicClosure w.1.Completion)ˣ)
      (MonoidHom.toAdditive
        ((Units.map ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom.toMonoidHom).comp
          (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)).subtype)),
    fun σ => LinearMap.ext fun (ζ : Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) =>
      congrArg Additive.ofMul
        (Units.ext (gsRealFamily_apply S ιr w σ
          (((Additive.toMul ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
            maxUnramifiedOutside K.1 ℚ̄ S)))⟩

theorem gsRealRootsToUnits_injective (w : {v : InfinitePlace K.1 // v.IsReal}) :
    Function.Injective (gsRealRootsToUnits S ιr n w).hom := by
  intro a b hab
  have h := congrArg (fun x => ((Additive.toMul x : (AlgebraicClosure w.1.Completion)ˣ) :
    AlgebraicClosure w.1.Completion)) hab
  change ιr w _ = ιr w _ at h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact (ιr w).toRingHom.injective h

def gsRealInvRootsQZ (w : {v : InfinitePlace K.1 // v.IsReal}) :
    cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S n)) 2 →+ QZ :=
  (realInv w.1.Completion (AlgebraicClosure w.1.Completion) (infAlgClosure_finrank_le_two w.1)
    (infAlgClosure_mul_mem_range_norm w.1)).comp
      (cohomologyMap (gsRealRootsToUnits S ιr n w) 2).hom.toAddMonoidHom

theorem gsRealInvRootsQZ_apply (w : {v : InfinitePlace K.1 // v.IsReal})
    (z : cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S n)) 2) :
    gsRealInvRootsQZ S ιr n w z =
      realInv w.1.Completion (AlgebraicClosure w.1.Completion) (infAlgClosure_finrank_le_two w.1)
        (infAlgClosure_mul_mem_range_norm w.1) ((cohomologyMap (gsRealRootsToUnits S ιr n w) 2).hom z) :=
  rfl

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]

variable [NeZero n] (hD : Nonempty (gsRoots S n ≃+ ZMod n)) (hM : ∀ m : M, n • m = 0)

set_option maxHeartbeats 400000 in
include hD hM in

theorem surjective_gsRealPairing_zero (w : {v : InfinitePlace K.1 // v.IsReal}) :
    Function.Surjective
      (ptLocalPairing (gsRealFamily S ιr) (gsRoots S n) M (gsRealInvRootsQZ S ιr n) w
        (show 0 + 2 = 2 from rfl)) := fun χ => by
  have : IsDiscreteRep (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) :=
    isDiscreteRep_galUnits
  have : IsDiscreteRep (cartierDual w.1.Completion (AlgebraicClosure w.1.Completion)
      (Rep.res (gsRealFamily S ιr w).toMonoidHom M)) := isDiscreteRep_cartierDual _
  have key := exists_orderTwo_pairing_zero (gsRealFamily S ιr w) (gsRoots S n)
    (gsRealRootsToUnits S ιr n w) M ?h2 ?hN (c := realConj w.1 w.2) ?hG ?hc ?hneg ?hconj ?hroots
    (gsRealInvRootsQZ S ιr n w) ?hinv hD ?hρ hM χ
  case h2 => exact infAlgClosure_finrank_le_two w.1
  case hN => exact infAlgClosure_mul_mem_range_norm w.1
  case hG => exact eq_one_or_eq_realConj w.1 w.2
  case hc => exact realConj_ne_one w.1 w.2
  case hneg => exact neg_one_not_mem_range_norm_infAlgClosure w.1 w.2
  case hconj => exact realConj_galUnits_of_torsion w.1 w.2
  case hroots => exact nonempty_addEquiv_galRootsOfUnity_infAlgClosure w.1
  case hinv => exact gsRealInvRootsQZ_apply S ιr n w
  case hρ => exact gsRealRootsToUnits_injective S ιr n w
  obtain ⟨ξ, hξ⟩ := key
  exact ⟨ξ, AddMonoidHom.ext fun η => (ptLocalPairing_apply _ _ _ _ _ _ _ _).trans (hξ η)⟩

set_option maxHeartbeats 400000 in
include hD hM in

theorem exists_gsRealPairing_two (w : {v : InfinitePlace K.1 // v.IsReal})
    (χ : cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom (dualRep (gsRoots S n) M)) 0 →+ QZ)
    (hχ : ∀ x ∈ normClasses (Rep.res (gsRealFamily S ιr w).toMonoidHom (dualRep (gsRoots S n) M)),
      χ x = 0) :
    ∃ ξ, ptLocalPairing (gsRealFamily S ιr) (gsRoots S n) M (gsRealInvRootsQZ S ιr n) w
      (show 2 + 0 = 2 from rfl) ξ = χ := by
  have : IsDiscreteRep (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) :=
    isDiscreteRep_galUnits
  have : IsDiscreteRep (cartierDual w.1.Completion (AlgebraicClosure w.1.Completion)
      (Rep.res (gsRealFamily S ιr w).toMonoidHom M)) := isDiscreteRep_cartierDual _
  have key := exists_orderTwo_pairing_two (gsRealFamily S ιr w) (gsRoots S n)
    (gsRealRootsToUnits S ιr n w) M ?h2 ?hN (c := realConj w.1 w.2) ?hG ?hc ?hneg ?hconj ?hroots
    (gsRealInvRootsQZ S ιr n w) ?hinv hD ?hρ hM χ hχ
  case h2 => exact infAlgClosure_finrank_le_two w.1
  case hN => exact infAlgClosure_mul_mem_range_norm w.1
  case hG => exact eq_one_or_eq_realConj w.1 w.2
  case hc => exact realConj_ne_one w.1 w.2
  case hneg => exact neg_one_not_mem_range_norm_infAlgClosure w.1 w.2
  case hconj => exact realConj_galUnits_of_torsion w.1 w.2
  case hroots => exact nonempty_addEquiv_galRootsOfUnity_infAlgClosure w.1
  case hinv => exact gsRealInvRootsQZ_apply S ιr n w
  case hρ => exact gsRealRootsToUnits_injective S ιr n w
  obtain ⟨ξ, hξ⟩ := key
  exact ⟨ξ, AddMonoidHom.ext fun η => (ptLocalPairing_apply _ _ _ _ _ _ _ _).trans (hξ η)⟩

end GS

end GroundTheory.ProfCoh
