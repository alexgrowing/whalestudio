import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.OrderTwoTate
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Involution OrderTwo

attribute [local instance 2000] Rep.hV2

section Transfer

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F))
  {n : ℕ} [NeZero n] (hMn : ∀ m : M, n • m = 0) (e : galRootsOfUnity.{0} F Ω n ≃+ ZMod n)

def cartierDualRoots : cartierDual F Ω M →+ (M →+ galRootsOfUnity.{0} F Ω n) :=
  (uliftIntLinearEquivAddHom M (galRootsOfUnity.{0} F Ω n)).toAddMonoidHom.comp
    (cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).inv.hom.toLinearMap.toAddMonoidHom

omit [NeZero n] in
theorem rootsOfUnityToUnits_cartierDualRoots (φ : cartierDual F Ω M) (m : M) :
    (rootsOfUnityToUnits F Ω n).hom (cartierDualRoots M hMn φ m) =
      (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m := by
  have h := cartierDualIsoHomRootsOfUnityOfNsmul_hom_apply M n hMn
    ((cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).inv.hom φ) m
  have hi := congrArg (fun f => (f.hom φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m)
    (cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).inv_hom_id
  exact h.symm.trans hi

def cartierDualToQZ : cartierDual F Ω M →+ (M →+ QZ) :=
  (AddMonoidHom.compHom ((zmodToQZ n).comp e.toAddMonoidHom)).comp (cartierDualRoots M hMn)

omit [NeZero n] in
theorem cartierDualToQZ_apply (φ : cartierDual F Ω M) (m : M) :
    cartierDualToQZ M hMn e φ m = zmodToQZ n (e (cartierDualRoots M hMn φ m)) :=
  rfl

theorem cartierDualToQZ_apply_eq_zero_iff (φ : cartierDual F Ω M) (m : M) :
    cartierDualToQZ M hMn e φ m = 0 ↔ (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m = 0 := by
  rw [cartierDualToQZ_apply, ← rootsOfUnityToUnits_cartierDualRoots M hMn,
    ← map_zero (zmodToQZ n), (zmodToQZ_injective (n := n)).eq_iff, ← map_zero e,
    e.injective.eq_iff, ← map_zero (rootsOfUnityToUnits F Ω n).hom,
    (rootsOfUnityToUnits_injective n).eq_iff]

theorem cartierDualToQZ_injective : Function.Injective (cartierDualToQZ M hMn e) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  apply LinearMap.ext
  intro m
  exact (cartierDualToQZ_apply_eq_zero_iff M hMn e φ m).1 (DFunLike.congr_fun hφ m)

theorem cartierDualToQZ_surjective : Function.Surjective (cartierDualToQZ M hMn e) := by
  intro f
  have hf : ∀ m, n • f m = 0 := fun m => by rw [← map_nsmul, hMn, map_zero]
  let ψ : M →ₗ[ULift.{0} ℤ] galRootsOfUnity.{0} F Ω n :=
    (uliftIntLinearEquivAddHom M (galRootsOfUnity.{0} F Ω n)).symm
      (e.symm.toAddMonoidHom.comp (zmodOfQZ f hf))
  refine ⟨(cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).hom.hom
    (show (Rep.ihom M).obj (galRootsOfUnity.{0} F Ω n) from ψ), ?_⟩
  ext m
  rw [cartierDualToQZ_apply]
  have hi := congrArg (fun g => (g.hom (show (Rep.ihom M).obj (galRootsOfUnity.{0} F Ω n) from ψ) :
      M →ₗ[ULift.{0} ℤ] galRootsOfUnity.{0} F Ω n) m)
    (cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).hom_inv_id
  have h : cartierDualRoots M hMn ((cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).hom.hom
      (show (Rep.ihom M).obj (galRootsOfUnity.{0} F Ω n) from ψ)) m = ψ m := hi
  rw [h]
  change zmodToQZ n (e (e.symm (zmodOfQZ f hf m))) = f m
  rw [e.apply_symm_apply, zmodToQZ_zmodOfQZ]

def cartierDualEquivQZ : cartierDual F Ω M ≃+ (M →+ QZ) :=
  AddEquiv.ofBijective (cartierDualToQZ M hMn e)
    ⟨cartierDualToQZ_injective M hMn e, cartierDualToQZ_surjective M hMn e⟩

end Transfer

section Equivariance

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F))
  {n : ℕ} [NeZero n] (hMn : ∀ m : M, n • m = 0) (e : galRootsOfUnity.{0} F Ω n ≃+ ZMod n)

omit [NeZero n] in

theorem cartierDualToQZ_act {c : Gal(Ω/F)} (hinv : c⁻¹ = c)
    (hconj : ∀ ζ : galUnits.{0} F Ω, n • ζ = 0 → (galUnits.{0} F Ω).ρ c ζ = -ζ)
    (φ : cartierDual F Ω M) :
    cartierDualToQZ M hMn e ((cartierDual F Ω M).ρ c φ) =
      dualInv (act M c) (cartierDualToQZ M hMn e φ) := by
  ext m
  rw [dualInv_apply, cartierDualToQZ_apply, cartierDualToQZ_apply, ← map_neg, ← map_neg]
  congr 2
  apply rootsOfUnityToUnits_injective n
  rw [map_neg, rootsOfUnityToUnits_cartierDualRoots, rootsOfUnityToUnits_cartierDualRoots,
    cartierDual_ρ_apply, hinv]
  apply hconj
  rw [← map_nsmul, hMn, map_zero]

end Equivariance

namespace QZ

theorem eq_mk_half_of_two_nsmul {q : QZ} (hq : 2 • q = 0) (hq0 : q ≠ 0) : q = QZ.mk (1 / 2) := by
  obtain ⟨m, hm⟩ := QZ.exists_eq_nsmul_mk_one_div (by norm_num) hq
  rw [hm] at hq0 ⊢
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · exfalso
    apply hq0
    rw [mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero]
  · rw [add_nsmul, one_nsmul, mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero, zero_add]
    norm_num

end QZ

section Invariant

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : F) ∉ Set.range (Algebra.norm F : Ω → F))

include hneg in

theorem realInv_cocycleTwo (t : galUnits.{0} F Ω) (ht : (galUnits.{0} F Ω).ρ c t = t)
    (h2t : 2 • t = 0) (q : QZ) (hq : 2 • q = 0) (hqt : q = 0 ↔ t = 0) :
    realInv F Ω h2 hN (cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc t ht)) = q := by
  by_cases ht0 : t = 0
  · have hz : cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc t ht) = 0 := by
      rw [cohomologyπ_cocycleTwo_eq_zero_iff]
      exact ⟨0, by rw [ht0, map_zero, add_zero]⟩
    rw [hz, map_zero, hqt.2 ht0]
  · have hq0 : q ≠ 0 := fun h => ht0 (hqt.1 h)
    rw [QZ.eq_mk_half_of_two_nsmul hq hq0]
    have hne : cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc t ht) ≠ 0 := by
      rw [Ne, cohomologyπ_cocycleTwo_eq_zero_iff]
      rintro ⟨m, hm⟩
      have hu : ((Additive.toMul t : Ωˣ) : Ω) = -1 := by
        have hsq : ((Additive.toMul t : Ωˣ) : Ω) * ((Additive.toMul t : Ωˣ) : Ω) = 1 := by
          rw [← Units.val_mul, ← toMul_add, ← two_nsmul, h2t, toMul_zero, Units.val_one]
        rcases mul_self_eq_one_iff.1 hsq with h | h
        · exfalso
          apply ht0
          apply Additive.toMul.injective
          exact Units.ext h
        · exact h
      have hnorm := coe_toMul_norm_galUnitsZ F Ω m
      rw [norm_apply (galUnitsZ F Ω) hG hc] at hnorm
      change ((Additive.toMul (m + (galUnits.{0} F Ω).ρ c m) : Ωˣ) : Ω) = _ at hnorm
      rw [← hm, hu, ← map_one (algebraMap F Ω), ← map_neg] at hnorm
      exact hneg ⟨_, ((algebraMap F Ω).injective hnorm).symm⟩
    rw [realInv_apply]
    exact quadraticInvFun_of_ne_zero F Ω
      ((AddEquiv.map_ne_zero_iff (cohomologyULiftIntAddEquiv (galUnits.{0} F Ω) 2)).2 hne)

end Invariant

section Congr

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] {c : G} (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

theorem cohomologyπ_cocycleTwo_congr (A : Rep.{0} k G) [IsDiscreteRep A]
    {a b : A} (ha : A.ρ c a = a) (hb : A.ρ c b = b) (hab : a = b) :
    cohomologyπ A 2 (cocycleTwo A hG hc a ha) = cohomologyπ A 2 (cocycleTwo A hG hc b hb) := by
  subst hab
  rfl

end Congr

section Cup

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)

omit [FiniteDimensional F Ω] in

theorem cochainOf_cupCartier {p q : ℕ} (h : p + q = 2) (x : cocycles M p)
    (y : cocycles (cartierDual F Ω M) q) (s : Fin 2 → Gal(Ω/F)) :
    cochainOf _ (cocycleι _ 2 (HomologicalComplex.cyclesMap (cochainsMap (cartierPairing F Ω M)) 2
        (cupCocycles h x y))) s =
      ((((cartierDual F Ω M).ρ (Fin.partialProd s ⟨p, by omega⟩)
          (cochainOf _ (cocycleι _ q y) fun j : Fin q => s ⟨p + j, by omega⟩)) :
        M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (cochainOf M (cocycleι M p x) fun i : Fin p => s ⟨i, by omega⟩)) := by
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, cartierPairing_tmul]

theorem cupPairing_cocycleOne (α : M) (hα : α + M.ρ c α = 0) (β : cartierDual F Ω M)
    (hβ : β + (cartierDual F Ω M).ρ c β = 0) :
    ∃ ht, cupPairing (cartierPairing F Ω M) (show 1 + 1 = 2 from rfl)
        (cohomologyπ M 1 (cocycleOne M hG hc α hα))
        (cohomologyπ _ 1 (cocycleOne (cartierDual F Ω M) hG hc β hβ)) =
      cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc
        ((((cartierDual F Ω M).ρ c β) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) α) ht) := by
  set z := HomologicalComplex.cyclesMap (cochainsMap (cartierPairing F Ω M)) 2
    (cupCocycles (show 1 + 1 = 2 from rfl) (cocycleOne M hG hc α hα)
      (cocycleOne (cartierDual F Ω M) hG hc β hβ)) with hz
  have hval : ∀ g h : Gal(Ω/F), cochainOf _ (cocycleι _ 2 z) ![g, h] =
      ((((cartierDual F Ω M).ρ g) (cochainOne (cartierDual F Ω M) β ![h])) :
        M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (cochainOne M α ![g]) := by
    intro g h
    rw [hz, cochainOf_cupCartier, cochainOf_cocycleOne, cochainOf_cocycleOne]
    have e1 : (fun j : Fin 1 => (![g, h] : Fin 2 → Gal(Ω/F)) ⟨1 + j, by omega⟩) = ![h] := by
      funext j; fin_cases j; rfl
    have e2 : (fun i : Fin 1 => (![g, h] : Fin 2 → Gal(Ω/F)) ⟨i, by omega⟩) = ![g] := by
      funext i; fin_cases i; rfl
    have e3 : Fin.partialProd (![g, h] : Fin 2 → Gal(Ω/F)) ⟨1, by omega⟩ = g := by
      simp [Fin.partialProd]
    rw [e1, e2, e3]
  obtain ⟨ht, hzt⟩ := exists_eq_cocycleTwo_of_normalized (galUnits.{0} F Ω) hG hc z
    (fun g => by rw [hval, cochainOne_one, map_zero])
    (fun g => by rw [hval, cochainOne_one, map_zero, LinearMap.zero_apply])
  have hcc : cochainOf _ (cocycleι _ 2 z) ![c, c] =
      ((((cartierDual F Ω M).ρ c β) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) α) := by
    rw [hval, cochainOne_c _ hc, cochainOne_c _ hc]
  refine ⟨hcc ▸ ht, ?_⟩
  rw [cupPairing_cohomologyπ, ← hz]
  exact (congrArg (cohomologyπ _ 2).hom hzt).trans (cohomologyπ_cocycleTwo_congr hG hc _ _ _ hcc)

end Cup

section Cup2

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)

theorem cupPairing_cocycleTwo_H0 (a : M) (ha : M.ρ c a = a)
    (φ : (cartierDual F Ω M).ρ.invariants) :
    ∃ ht, cupPairing (cartierPairing F Ω M) (show 2 + 0 = 2 from rfl)
        (cohomologyπ M 2 (cocycleTwo M hG hc a ha)) ((H0Iso (cartierDual F Ω M)).inv.hom φ) =
      cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc
        (((φ : cartierDual F Ω M) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) a) ht) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv (cartierDual F Ω M) φ
  rw [← hz0]
  set z := HomologicalComplex.cyclesMap (cochainsMap (cartierPairing F Ω M)) 2
    (cupCocycles (show 2 + 0 = 2 from rfl) (cocycleTwo M hG hc a ha) z0) with hz
  have hval : ∀ g h : Gal(Ω/F), cochainOf _ (cocycleι _ 2 z) ![g, h] =
      (((φ : cartierDual F Ω M) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (cochainTwo M c a ![g, h])) := by
    intro g h
    rw [hz, cochainOf_cupCartier, cochainOf_cocycleTwo, hz0c, φ.2]
  obtain ⟨ht, hzt⟩ := exists_eq_cocycleTwo_of_normalized (galUnits.{0} F Ω) hG hc z
    (fun g => by rw [hval, cochainTwo_one_left M hc, map_zero])
    (fun g => by rw [hval, cochainTwo_one_right M hc, map_zero])
  have hcc : cochainOf _ (cocycleι _ 2 z) ![c, c] =
      (((φ : cartierDual F Ω M) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) a) := by
    rw [hval, cochainTwo_cc]
  refine ⟨hcc ▸ ht, ?_⟩
  rw [cupPairing_cohomologyπ, ← hz]
  exact (congrArg (cohomologyπ _ 2).hom hzt).trans (cohomologyπ_cocycleTwo_congr hG hc _ _ _ hcc)

theorem cupPairing_H0_cocycleTwo (a : M.ρ.invariants) (φ : cartierDual F Ω M)
    (hφ : (cartierDual F Ω M).ρ c φ = φ) :
    ∃ ht, cupPairing (cartierPairing F Ω M) (show 0 + 2 = 2 from rfl)
        ((H0Iso M).inv.hom a) (cohomologyπ _ 2 (cocycleTwo (cartierDual F Ω M) hG hc φ hφ)) =
      cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc
        ((φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (a : M)) ht) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv M a
  rw [← hz0]
  set z := HomologicalComplex.cyclesMap (cochainsMap (cartierPairing F Ω M)) 2
    (cupCocycles (show 0 + 2 = 2 from rfl) z0 (cocycleTwo (cartierDual F Ω M) hG hc φ hφ)) with hz
  have hval : ∀ g h : Gal(Ω/F), cochainOf _ (cocycleι _ 2 z) ![g, h] =
      ((cochainTwo (cartierDual F Ω M) c φ ![g, h] : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (a : M)) := by
    intro g h
    rw [hz, cochainOf_cupCartier, cochainOf_cocycleTwo, hz0c]
    have e1 : (fun j : Fin 2 => (![g, h] : Fin 2 → Gal(Ω/F)) ⟨0 + j, by omega⟩) = ![g, h] := by
      funext j; fin_cases j <;> rfl
    have e3 : Fin.partialProd (![g, h] : Fin 2 → Gal(Ω/F)) ⟨0, by omega⟩ = 1 := by
      simp [Fin.partialProd]
    rw [e1, e3, map_one, Module.End.one_apply]
  obtain ⟨ht, hzt⟩ := exists_eq_cocycleTwo_of_normalized (galUnits.{0} F Ω) hG hc z
    (fun g => by rw [hval, cochainTwo_one_left _ hc, LinearMap.zero_apply])
    (fun g => by rw [hval, cochainTwo_one_right _ hc, LinearMap.zero_apply])
  have hcc : cochainOf _ (cocycleι _ 2 z) ![c, c] =
      ((φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (a : M)) := by
    rw [hval, cochainTwo_cc]
  refine ⟨hcc ▸ ht, ?_⟩
  rw [cupPairing_cohomologyπ, ← hz]
  exact (congrArg (cohomologyπ _ 2).hom hzt).trans (cohomologyπ_cocycleTwo_congr hG hc _ _ _ hcc)

end Cup2

end GroundTheory.ProfCoh
