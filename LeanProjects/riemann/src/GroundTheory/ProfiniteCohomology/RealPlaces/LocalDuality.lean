import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityCup
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Involution OrderTwo

attribute [local instance 2000] Rep.hV2

section Neg

variable {M : Type*} [AddCommGroup M]

theorem Involution.dualInv_neg (σ : M →+ M) (f : M →+ QZ) : dualInv (-σ) f = -dualInv σ f := by
  ext x
  simp

end Neg

section Generic

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]

include hG hc in

theorem realDualityPairing_two_zero_eq_zero (x : cohomology M 2)
    (y : cohomology (cartierDual F Ω M) 0) (hy : y ∈ normClasses (cartierDual F Ω M)) :
    realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl) x y = 0 := by
  obtain ⟨b, hb, rfl⟩ := (mem_normClasses_iff _ y).1 hy
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective M 2 x
  obtain ⟨a, ha, e⟩ := exists_cohomologyπ_eq_cocycleTwo M hG hc z
  rw [e, realDualityPairing_apply]
  obtain ⟨ht, hcup⟩ := cupPairing_cocycleTwo_H0 M hG hc a ha ⟨_, hb⟩
  rw [hcup]
  convert map_zero (realInv F Ω h2 hN)
  rw [cohomologyπ_cocycleTwo_eq_zero_iff]
  refine ⟨(b : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) a, ?_⟩
  change ((((cartierDual F Ω M).ρ.norm b) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) a) = _
  rw [norm_apply _ hG hc, LinearMap.add_apply, cartierDual_ρ_apply, inv_eq_self hG hc, ha]

include hG hc in

theorem realDualityPairing_zero_two_eq_zero (x : cohomology M 0) (hx : x ∈ normClasses M)
    (y : cohomology (cartierDual F Ω M) 2) :
    realDualityPairing F Ω h2 hN M (show 0 + 2 = 2 from rfl) x y = 0 := by
  obtain ⟨b, hb, rfl⟩ := (mem_normClasses_iff _ x).1 hx
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 2 y
  obtain ⟨φ, hφ, e⟩ := exists_cohomologyπ_eq_cocycleTwo _ hG hc z
  rw [e, realDualityPairing_apply]
  obtain ⟨ht, hcup⟩ := cupPairing_H0_cocycleTwo M hG hc ⟨_, hb⟩ φ hφ
  rw [hcup]
  convert map_zero (realInv F Ω h2 hN)
  rw [cohomologyπ_cocycleTwo_eq_zero_iff]
  refine ⟨(φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) b, ?_⟩
  have hφb : (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (M.ρ c b) =
      (galUnits.{0} F Ω).ρ c ((φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) b) := by
    conv_lhs => rw [← hφ]
    rw [cartierDual_ρ_apply, inv_eq_self hG hc, ← Module.End.mul_apply, ← map_mul,
      mul_self_eq_one hG hc, map_one, Module.End.one_apply]
  change (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (M.ρ.norm b) = _
  rw [norm_apply _ hG hc, map_add, hφb]

end Generic

section Lifted

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]

def realDualityPairingTwoZero :
    cohomology M 2 →+ cohomologyTateZero (cartierDual F Ω M) →+ QZ where
  toFun x := QuotientAddGroup.lift (normClasses (cartierDual F Ω M)).toAddSubgroup
    (realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl) x)
    (fun y hy => realDualityPairing_two_zero_eq_zero h2 hN hG hc M x y hy)
  map_zero' := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact DFunLike.congr_fun (map_zero (realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl))) y
  map_add' x x' := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact DFunLike.congr_fun (map_add (realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl)) x x') y

theorem realDualityPairingTwoZero_mk (x : cohomology M 2) (y : cohomology (cartierDual F Ω M) 0) :
    realDualityPairingTwoZero h2 hN hG hc M x (Submodule.Quotient.mk y) =
      realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl) x y :=
  rfl

def realDualityPairingZeroTwo :
    cohomologyTateZero M →+ cohomology (cartierDual F Ω M) 2 →+ QZ :=
  QuotientAddGroup.lift (normClasses M).toAddSubgroup
    (realDualityPairing F Ω h2 hN M (show 0 + 2 = 2 from rfl))
    (fun x hx => by
      ext y
      exact realDualityPairing_zero_two_eq_zero h2 hN hG hc M x hx y)

theorem realDualityPairingZeroTwo_mk (x : cohomology M 0) (y : cohomology (cartierDual F Ω M) 2) :
    realDualityPairingZeroTwo h2 hN hG hc M (Submodule.Quotient.mk x) y =
      realDualityPairing F Ω h2 hN M (show 0 + 2 = 2 from rfl) x y :=
  rfl

end Lifted

section Duality

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : F) ∉ Set.range (Algebra.norm F : Ω → F))
  (hconj : ∀ ζ : galUnits.{0} F Ω, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (galUnits.{0} F Ω).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (galRootsOfUnity.{0} F Ω k ≃+ ZMod k))
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]

omit [IsDiscreteRep M] [Finite M] in
include hneg in

theorem realInv_cocycleTwo_eq_cartierDualToQZ {n : ℕ} [NeZero n] (hMn : ∀ m : M, n • m = 0)
    (e : galRootsOfUnity.{0} F Ω n ≃+ ZMod n) (φ : cartierDual F Ω M) (m : M)
    (hq : 2 • cartierDualToQZ M hMn e φ m = 0) (t : galUnits.{0} F Ω)
    (htφ : t = (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m ∨
      t = -(φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m)
    (ht : (galUnits.{0} F Ω).ρ c t = t) :
    realInv F Ω h2 hN (cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc t ht)) =
      cartierDualToQZ M hMn e φ m := by
  have h2φ : 2 • (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m = 0 := by
    rw [← map_nsmul, ← cartierDualToQZ_apply_eq_zero_iff M hMn e, map_nsmul]
    exact hq
  have ht0 : t = 0 ↔ (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m = 0 := by
    rcases htφ with rfl | rfl
    · rfl
    · exact neg_eq_zero
  refine realInv_cocycleTwo h2 hN hG hc hneg t ht ?_ _ hq ?_
  · rcases htφ with rfl | rfl
    · exact h2φ
    · rw [two_nsmul] at h2φ ⊢
      rw [← neg_add, h2φ, neg_zero]
  · rw [ht0]
    exact cartierDualToQZ_apply_eq_zero_iff M hMn e φ m

include hneg hconj hroots in

theorem realDualityPairingTwoZero_eq_tatePair :
    ∃ (e : tateQuot (act M c) ≃+ cohomology M 2)
      (e' : tateQuot (dualInv (act M c)) ≃+ cohomologyTateZero (cartierDual F Ω M)),
      ∀ x y, realDualityPairingTwoZero h2 hN hG hc M (e x) (e' y) = tatePair (act M c) x y := by
  have : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  have hMn : ∀ m : M, Nat.card M • m = 0 := fun m => card_nsmul_eq_zero'
  obtain ⟨e⟩ := hroots (Nat.card M) Nat.card_pos
  set T := cartierDualEquivQZ M hMn e with hT
  have hact : ∀ φ, T ((cartierDual F Ω M).ρ c φ) = dualInv (act M c) (T φ) := fun φ =>
    cartierDualToQZ_act M hMn e (OrderTwo.inv_eq_self hG hc) (fun ζ hζ => hconj ζ ⟨_, Nat.card_pos, hζ⟩) φ
  have he0 : ∀ f, T.symm (dualInv (act M c) f) = act (cartierDual F Ω M) c (T.symm f) := fun f => by
    apply T.injective
    rw [T.apply_symm_apply]
    change _ = T ((cartierDual F Ω M).ρ c (T.symm f))
    rw [hact, T.apply_symm_apply]
  refine ⟨h2EquivOfOrderTwo M hG hc, (tateQuotCongr T.symm he0).trans (cohomZeroEquivContinuous (cartierDual F Ω M) hG hc),
    fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddEquiv.trans_apply, tateQuotCongr_mk, h2Equiv_mk, h0Equiv_mk, realDualityPairingTwoZero_mk,
    realDualityPairing_apply, tatePair_mk]
  obtain ⟨ht, hcup⟩ := cupPairing_cocycleTwo_H0 M hG hc (a : M) ((mem_fixedSub_act M).1 a.2)
    ⟨_, mem_invariants_of_fixed (cartierDual F Ω M) hG
      ((mem_fixedSub_act _).1 (fixedSubCongr T.symm he0 f).2)⟩
  rw [hcup]
  have hTf : cartierDualToQZ M hMn e (T.symm f) = f := T.apply_symm_apply f
  have hq : 2 • cartierDualToQZ M hMn e (T.symm f) a = 0 := by
    rw [hTf]
    exact two_nsmul_fixedPair (act M c) a f
  refine (realInv_cocycleTwo_eq_cartierDualToQZ h2 hN hG hc hneg M hMn e (T.symm f) a hq _
    (Or.inl rfl) ht).trans ?_
  rw [hTf]

include hneg hconj hroots in

theorem realDualityPairingZeroTwo_eq_tatePair :
    ∃ (e : tateQuot (act M c) ≃+ cohomologyTateZero M)
      (e' : tateQuot (dualInv (act M c)) ≃+ cohomology (cartierDual F Ω M) 2),
      ∀ x y, realDualityPairingZeroTwo h2 hN hG hc M (e x) (e' y) = tatePair (act M c) x y := by
  have : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  have hMn : ∀ m : M, Nat.card M • m = 0 := fun m => card_nsmul_eq_zero'
  obtain ⟨e⟩ := hroots (Nat.card M) Nat.card_pos
  set T := cartierDualEquivQZ M hMn e with hT
  have hact : ∀ φ, T ((cartierDual F Ω M).ρ c φ) = dualInv (act M c) (T φ) := fun φ =>
    cartierDualToQZ_act M hMn e (OrderTwo.inv_eq_self hG hc) (fun ζ hζ => hconj ζ ⟨_, Nat.card_pos, hζ⟩) φ
  have he0 : ∀ f, T.symm (dualInv (act M c) f) = act (cartierDual F Ω M) c (T.symm f) := fun f => by
    apply T.injective
    rw [T.apply_symm_apply]
    change _ = T ((cartierDual F Ω M).ρ c (T.symm f))
    rw [hact, T.apply_symm_apply]
  refine ⟨cohomZeroEquivContinuous M hG hc, (tateQuotCongr T.symm he0).trans (h2EquivOfOrderTwo (cartierDual F Ω M) hG hc),
    fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddEquiv.trans_apply, tateQuotCongr_mk, h2Equiv_mk, h0Equiv_mk, realDualityPairingZeroTwo_mk,
    realDualityPairing_apply, tatePair_mk]
  obtain ⟨ht, hcup⟩ := cupPairing_H0_cocycleTwo M hG hc
    ⟨_, mem_invariants_of_fixed M hG ((mem_fixedSub_act M).1 a.2)⟩
    ((fixedSubCongr T.symm he0 f : fixedSub _) : cartierDual F Ω M)
    ((mem_fixedSub_act _).1 (fixedSubCongr T.symm he0 f).2)
  rw [hcup]
  have hTf : cartierDualToQZ M hMn e ((fixedSubCongr T.symm he0 f : fixedSub _) : cartierDual F Ω M) =
      f := T.apply_symm_apply f
  have hq : 2 • cartierDualToQZ M hMn e
      ((fixedSubCongr T.symm he0 f : fixedSub _) : cartierDual F Ω M) a = 0 := by
    rw [hTf]
    exact two_nsmul_fixedPair (act M c) a f
  refine (realInv_cocycleTwo_eq_cartierDualToQZ h2 hN hG hc hneg M hMn e _ a hq _
    (Or.inl rfl) ht).trans ?_
  rw [hTf]

include hG hc hneg hconj hroots in

theorem realDualityPairing_one_eq_tatePair :
    ∃ (e : tateQuot (-act M c) ≃+ cohomology M 1)
      (e' : tateQuot (dualInv (-act M c)) ≃+ cohomology (cartierDual F Ω M) 1),
      ∀ x y, realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl) (e x) (e' y) =
        tatePair (-act M c) x y := by
  have : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  have hMn : ∀ m : M, Nat.card M • m = 0 := fun m => card_nsmul_eq_zero'
  obtain ⟨e⟩ := hroots (Nat.card M) Nat.card_pos
  set T := cartierDualEquivQZ M hMn e with hT
  have hact : ∀ φ, T ((cartierDual F Ω M).ρ c φ) = dualInv (act M c) (T φ) := fun φ =>
    cartierDualToQZ_act M hMn e (OrderTwo.inv_eq_self hG hc) (fun ζ hζ => hconj ζ ⟨_, Nat.card_pos, hζ⟩) φ
  have he1 : ∀ f, T.symm (dualInv (-act M c) f) = (-act (cartierDual F Ω M) c) (T.symm f) :=
    fun f => by
      apply T.injective
      rw [T.apply_symm_apply, AddMonoidHom.neg_apply, map_neg, dualInv_neg]
      change _ = -T ((cartierDual F Ω M).ρ c (T.symm f))
      rw [hact, T.apply_symm_apply]
  refine ⟨h1EquivOfOrderTwo M hG hc, (tateQuotCongr T.symm he1).trans (h1EquivOfOrderTwo (cartierDual F Ω M) hG hc),
    fun x y => ?_⟩
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddEquiv.trans_apply, tateQuotCongr_mk, h1Equiv_mk, h1Equiv_mk, realDualityPairing_apply,
    tatePair_mk]
  set β : cartierDual F Ω M := ((fixedSubCongr T.symm he1 f : fixedSub _) : cartierDual F Ω M)
    with hβdef
  obtain ⟨ht, hcup⟩ := cupPairing_cocycleOne M hG hc (α : M) ((mem_fixedSub_neg_act M).1 α.2)
    β ((mem_fixedSub_neg_act _).1 (fixedSubCongr T.symm he1 f).2)
  rw [hcup]
  have hTf : cartierDualToQZ M hMn e β = f := T.apply_symm_apply f
  have hq : 2 • cartierDualToQZ M hMn e β α = 0 := by
    rw [hTf]
    exact two_nsmul_fixedPair (-act M c) α f
  have hβ : (cartierDual F Ω M).ρ c β = -β :=
    eq_neg_of_add_eq_zero_right ((mem_fixedSub_neg_act _).1 (fixedSubCongr T.symm he1 f).2)
  refine (realInv_cocycleTwo_eq_cartierDualToQZ h2 hN hG hc hneg M hMn e β α hq _
    (Or.inr (by rw [hβ]; rfl)) ht).trans ?_
  rw [hTf]

include hG hc hneg hconj hroots in

theorem realDualityPairing_one_bijective :
    Function.Bijective (realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl)) := by
  obtain ⟨e, e', h⟩ := realDualityPairing_one_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_of_pairing_eq _ _ e e' h tatePair_bijective

include hG hc hneg hconj hroots in

theorem realDualityPairing_one_flip_bijective :
    Function.Bijective (realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl)).flip := by
  obtain ⟨e, e', h⟩ := realDualityPairing_one_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_flip_of_pairing_eq _ _ e e' h tatePair_flip_bijective

include hneg hconj hroots in

theorem realDualityPairingTwoZero_bijective :
    Function.Bijective (realDualityPairingTwoZero h2 hN hG hc M) := by
  obtain ⟨e, e', h⟩ := realDualityPairingTwoZero_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_of_pairing_eq _ _ e e' h tatePair_bijective

include hneg hconj hroots in

theorem realDualityPairingTwoZero_flip_bijective :
    Function.Bijective (realDualityPairingTwoZero h2 hN hG hc M).flip := by
  obtain ⟨e, e', h⟩ := realDualityPairingTwoZero_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_flip_of_pairing_eq _ _ e e' h tatePair_flip_bijective

include hneg hconj hroots in

theorem realDualityPairingZeroTwo_bijective :
    Function.Bijective (realDualityPairingZeroTwo h2 hN hG hc M) := by
  obtain ⟨e, e', h⟩ := realDualityPairingZeroTwo_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_of_pairing_eq _ _ e e' h tatePair_bijective

include hneg hconj hroots in

theorem realDualityPairingZeroTwo_flip_bijective :
    Function.Bijective (realDualityPairingZeroTwo h2 hN hG hc M).flip := by
  obtain ⟨e, e', h⟩ := realDualityPairingZeroTwo_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_flip_of_pairing_eq _ _ e e' h tatePair_flip_bijective

end Duality

section Values

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : F) ∉ Set.range (Algebra.norm F : Ω → F))
  (hconj : ∀ ζ : galUnits.{0} F Ω, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (galUnits.{0} F Ω).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (galRootsOfUnity.{0} F Ω k ≃+ ZMod k))
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]

end Values

section Bundle

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : F) ∉ Set.range (Algebra.norm F : Ω → F))
  (hconj : ∀ ζ : galUnits.{0} F Ω, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (galUnits.{0} F Ω).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (galRootsOfUnity.{0} F Ω k ≃+ ZMod k))
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]

include hneg hconj hroots in

theorem real_local_duality_of_orderTwo :
    (Function.Bijective (realDualityPairingZeroTwo h2 hN hG hc M) ∧
      Function.Bijective (realDualityPairingZeroTwo h2 hN hG hc M).flip) ∧
    (Function.Bijective (realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl)) ∧
      Function.Bijective (realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl)).flip) ∧
    (Function.Bijective (realDualityPairingTwoZero h2 hN hG hc M) ∧
      Function.Bijective (realDualityPairingTwoZero h2 hN hG hc M).flip) :=
  ⟨⟨realDualityPairingZeroTwo_bijective h2 hN hG hc hneg hconj hroots M,
      realDualityPairingZeroTwo_flip_bijective h2 hN hG hc hneg hconj hroots M⟩,
    ⟨realDualityPairing_one_bijective h2 hN hG hc hneg hconj hroots M,
      realDualityPairing_one_flip_bijective h2 hN hG hc hneg hconj hroots M⟩,
    ⟨realDualityPairingTwoZero_bijective h2 hN hG hc hneg hconj hroots M,
      realDualityPairingTwoZero_flip_bijective h2 hN hG hc hneg hconj hroots M⟩⟩

end Bundle

end GroundTheory.ProfCoh
