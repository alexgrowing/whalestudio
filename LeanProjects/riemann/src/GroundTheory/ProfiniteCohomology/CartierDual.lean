import Mathlib
import GroundTheory.ProfiniteCohomology.CartierDualDefs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section ULiftInt

attribute [-instance] ULift.smulLeft ULift.module

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module (ULift.{u} ℤ) A]
  [Module (ULift.{u} ℤ) B]

variable (A B) in

def uliftIntLinearEquivAddHom : (A →ₗ[ULift.{u} ℤ] B) ≃+ (A →+ B) where
  toFun f := f.toAddMonoidHom
  invFun g :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r a => by
        obtain ⟨k⟩ := r
        have h : (ULift.up k : ULift.{u} ℤ) = ((k : ℤ) : ULift.{u} ℤ) := by
          ext
          simp
        rw [RingHom.id_apply, h, Int.cast_smul_eq_zsmul (ULift.{u} ℤ) k a,
          Int.cast_smul_eq_zsmul (ULift.{u} ℤ) k (g a)]
        exact map_zsmul g k a }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem uliftIntLinearEquivAddHom_apply (f : A →ₗ[ULift.{u} ℤ] B) (a : A) :
    uliftIntLinearEquivAddHom A B f a = f a :=
  rfl

@[simp]
theorem uliftIntLinearEquivAddHom_symm_apply (g : A →+ B) (a : A) :
    (uliftIntLinearEquivAddHom A B).symm g a = g a :=
  rfl

end ULiftInt

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

section MonoidHom

variable (K L) in

def cartierDualEquivMonoidHom (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    (M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) ≃ (Multiplicative M →* Lˣ) :=
  (uliftIntLinearEquivAddHom M (Additive Lˣ)).toEquiv.trans AddMonoidHom.toMultiplicativeLeft

@[simp]
theorem cartierDualEquivMonoidHom_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (m : M) :
    cartierDualEquivMonoidHom K L M f (Multiplicative.ofAdd m) = Additive.toMul (f m) :=
  rfl

@[simp]
theorem cartierDualEquivMonoidHom_symm_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    (φ : Multiplicative M →* Lˣ) (m : M) :
    (cartierDualEquivMonoidHom K L M).symm φ m = Additive.ofMul (φ (Multiplicative.ofAdd m)) :=
  rfl

end MonoidHom

section RootsOfUnity

theorem cartierDual_pow_eq_one {M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)} {n : ℕ}
    (hn : ∀ m : M, n • m = 0) (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (m : M) :
    (Additive.toMul (α := Lˣ) (f m)) ^ n = 1 := by
  change (cartierDualEquivMonoidHom K L M f (Multiplicative.ofAdd m)) ^ n = 1
  rw [← map_pow, ← ofAdd_nsmul, hn m, ofAdd_zero, map_one]

theorem bijective_ihom_map_rootsOfUnityToUnits (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) {n : ℕ}
    (hn : ∀ m : M, n • m = 0) :
    Function.Bijective ((Rep.ihom M).map (rootsOfUnityToUnits K L n)).hom := by
  refine ⟨fun f g h => ?_, fun f₀ => ?_⟩
  · refine LinearMap.ext fun m => ?_
    have := LinearMap.congr_fun h m
    exact Additive.toMul.injective (Subtype.ext (congrArg (Additive.toMul (α := Lˣ)) this))
  · let f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f₀
    let g : M →+ Additive (rootsOfUnity n L) :=
      { toFun := fun m => Additive.ofMul
          ⟨Additive.toMul (α := Lˣ) (f m), (mem_rootsOfUnity n _).2 (cartierDual_pow_eq_one hn f m)⟩
        map_zero' := by
          apply Additive.toMul.injective
          apply Subtype.ext
          change Additive.toMul (α := Lˣ) (f 0) = 1
          rw [map_zero]
          rfl
        map_add' := fun a b => by
          apply Additive.toMul.injective
          apply Subtype.ext
          change Additive.toMul (α := Lˣ) (f (a + b)) =
            Additive.toMul (α := Lˣ) (f a) * Additive.toMul (α := Lˣ) (f b)
          rw [map_add]
          rfl }
    refine ⟨(uliftIntLinearEquivAddHom M (galRootsOfUnity.{u} K L n)).symm g, ?_⟩
    refine LinearMap.ext fun m => ?_
    rfl

variable (K L) in

def cartierDualIsoHomRootsOfUnityOfNsmul (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (n : ℕ)
    (hn : ∀ m : M, n • m = 0) :
    (Rep.ihom M).obj (galRootsOfUnity.{u} K L n) ≅ cartierDual K L M :=
  Rep.isoOfBijective ((Rep.ihom M).map (rootsOfUnityToUnits K L n))
    (bijective_ihom_map_rootsOfUnityToUnits M hn)

@[simp]
theorem cartierDualIsoHomRootsOfUnityOfNsmul_hom_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    (n : ℕ) (hn : ∀ m : M, n • m = 0) (f : M →ₗ[ULift.{u} ℤ] galRootsOfUnity.{u} K L n) (m : M) :
    ((cartierDualIsoHomRootsOfUnityOfNsmul K L M n hn).hom.hom f :
      M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) m = (rootsOfUnityToUnits K L n).hom (f m) :=
  rfl

variable (K L) in

def cartierDualIsoHomRootsOfUnity (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    (Rep.ihom M).obj (galRootsOfUnity.{u} K L (AddMonoid.exponent M)) ≅ cartierDual K L M :=
  cartierDualIsoHomRootsOfUnityOfNsmul K L M _ (AddMonoid.exponent_nsmul_eq_zero)

end RootsOfUnity

section Finite

variable (K L) in

instance finite_cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M] :
    Finite (cartierDual K L M) := by
  have : NeZero (AddMonoid.exponent M) := ⟨AddMonoid.exponent_ne_zero_of_finite⟩
  let F : (M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) → M → rootsOfUnity (AddMonoid.exponent M) L :=
    fun f m => ⟨Additive.toMul (α := Lˣ) (f m), (mem_rootsOfUnity _ _).2
      (cartierDual_pow_eq_one AddMonoid.exponent_nsmul_eq_zero f m)⟩
  refine Finite.of_injective (β := M → rootsOfUnity (AddMonoid.exponent M) L) F fun f g h => ?_
  refine LinearMap.ext fun m => ?_
  have := congrArg (fun x : rootsOfUnity (AddMonoid.exponent M) L => (x : Lˣ)) (congrFun h m)
  exact Additive.toMul.injective this

instance finite_cartierDual_cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M] :
    Finite (cartierDual K L (cartierDual K L M)) :=
  have : Finite (cartierDual K L M) := finite_cartierDual K L M
  finite_cartierDual K L _

instance isDiscreteRep_cartierDual [Algebra.IsIntegral K L] (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    [Finite M] [IsDiscreteRep M] : IsDiscreteRep (cartierDual K L M) := by
  refine ⟨fun f => ?_⟩
  let f' : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f
  refine Subgroup.isOpen_mono (H₁ := ⨅ m : M, stabilizer M.ρ m ⊓
      stabilizer (galUnits.{u} K L).ρ (f' m)) (fun σ hσ => ?_) ?_
  · rw [mem_stabilizer]
    refine LinearMap.ext fun m => ?_
    have hm := Subgroup.mem_iInf.1 hσ m
    rw [Subgroup.mem_inf, mem_stabilizer, mem_stabilizer] at hm
    change (galUnits.{u} K L).ρ σ (f' (M.ρ σ⁻¹ m)) = f' m
    have h1 : M.ρ σ⁻¹ m = m := by
      conv_lhs => rw [← hm.1]
      exact Representation.inv_self_apply _ _ _
    rw [h1, hm.2]
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun m => by
      rw [Subgroup.coe_inf]
      exact (isOpen_stabilizer M m).inter (isOpen_stabilizer (galUnits.{u} K L) (f' m))

theorem card_cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    Nat.card (cartierDual K L M) = Nat.card M := by
  have : HasEnoughRootsOfUnity L (Monoid.exponent (Multiplicative M)) := by
    rwa [Monoid.exponent_multiplicative]
  calc Nat.card (cartierDual K L M) = Nat.card (Multiplicative M →* Lˣ) :=
        Nat.card_congr (cartierDualEquivMonoidHom K L M)
    _ = Nat.card (Multiplicative M) :=
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative M) L
    _ = Nat.card M := Nat.card_congr Multiplicative.toAdd

variable (K) in

theorem hasEnoughRootsOfUnity_exponent_of_isSepClosed [IsSepClosed L] (M : Type*)
    [AddCommGroup M] [Finite M] (h : (Nat.card M : K) ≠ 0) :
    HasEnoughRootsOfUnity L (AddMonoid.exponent M) := by
  have hdvd : AddMonoid.exponent M ∣ Nat.card M := AddGroup.exponent_dvd_nat_card
  have hK : (AddMonoid.exponent M : K) ≠ 0 := by
    obtain ⟨c, hc⟩ := hdvd
    intro h0
    apply h
    rw [hc, Nat.cast_mul, h0, zero_mul]
  have : NeZero (AddMonoid.exponent M : L) := ⟨by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero (algebraMap K L)).2 hK⟩
  infer_instance

end Finite

section Pairing

variable (K L) [Algebra.IsIntegral K L]

def cartierPairingDiscrete (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M] [IsDiscreteRep M] :
    (⟨M ⊗ cartierDual K L M, (isDiscreteRep_apply _).2 inferInstance⟩ :
      DiscreteRep.{u} (ULift.{u} ℤ) Gal(L/K)) ⟶
      ⟨galUnits.{u} K L, (isDiscreteRep_apply _).2 inferInstance⟩ :=
  ObjectProperty.homMk (cartierPairing K L M)

variable {K L} in
@[simp]
theorem cartierPairingDiscrete_hom (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [IsDiscreteRep M] : (cartierPairingDiscrete K L M).hom = cartierPairing K L M :=
  rfl

end Pairing

section Biduality

theorem eq_zero_of_forall_cartierDual_apply_eq_zero {M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)}
    [Finite M] [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] {m : M}
    (h : ∀ f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L, f m = 0) : m = 0 := by
  have : HasEnoughRootsOfUnity L (Monoid.exponent (Multiplicative M)) := by
    rwa [Monoid.exponent_multiplicative]
  by_contra hm
  have hm' : Multiplicative.ofAdd m ≠ 1 := fun h1 => hm (Multiplicative.ofAdd.injective h1)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative M) L hm'
  apply hφ
  have := h ((cartierDualEquivMonoidHom K L M).symm φ)
  rw [cartierDualEquivMonoidHom_symm_apply] at this
  exact Additive.ofMul.injective this

theorem exponent_cartierDual_dvd (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    AddMonoid.exponent (cartierDual K L M) ∣ AddMonoid.exponent M := by
  refine AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero fun f => ?_
  let f' : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f
  change AddMonoid.exponent M • f' = 0
  refine LinearMap.ext fun m => ?_
  rw [LinearMap.smul_apply, ← map_nsmul, AddMonoid.exponent_nsmul_eq_zero, map_zero]
  rfl

theorem hasEnoughRootsOfUnity_exponent_cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    [Finite M] [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    HasEnoughRootsOfUnity L (AddMonoid.exponent (cartierDual K L M)) := by
  have : NeZero (AddMonoid.exponent M) := ⟨AddMonoid.exponent_ne_zero_of_finite⟩
  exact HasEnoughRootsOfUnity.of_dvd L (exponent_cartierDual_dvd M)

theorem toCartierDualCartierDual_bijective (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    Function.Bijective (toCartierDualCartierDual K L M).hom := by
  have := hasEnoughRootsOfUnity_exponent_cartierDual (K := K) (L := L) M
  have : Finite (cartierDual K L M) := finite_cartierDual K L M
  have : Finite (cartierDual K L (cartierDual K L M)) := finite_cartierDual K L _
  rw [Nat.bijective_iff_injective_and_card, card_cartierDual, card_cartierDual]
  refine ⟨(injective_iff_map_eq_zero _).2 fun m hm => ?_, rfl⟩
  refine eq_zero_of_forall_cartierDual_apply_eq_zero (K := K) (L := L) fun f => ?_
  have := LinearMap.congr_fun hm f
  exact this

variable (K L) in

def cartierBidualityIso (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    M ≅ cartierDual K L (cartierDual K L M) :=
  Rep.isoOfBijective (toCartierDualCartierDual K L M) (toCartierDualCartierDual_bijective M)

@[simp]
theorem cartierBidualityIso_hom (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    (cartierBidualityIso K L M).hom = toCartierDualCartierDual K L M :=
  rfl

variable (K L) in

def cartierBidualityIsoOfIsSepClosed [IsSepClosed L] (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    [Finite M] (h : (Nat.card M : K) ≠ 0) : M ≅ cartierDual K L (cartierDual K L M) :=
  have := hasEnoughRootsOfUnity_exponent_of_isSepClosed K (L := L) M h
  cartierBidualityIso K L M

end Biduality

section Exact

attribute [local instance 3000] Submodule.Quotient.module

variable (K L) in

def cartierDualShortComplex (S : ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(L/K))) :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :=
  ShortComplex.mk (cartierDualMap (K := K) (L := L) S.g) (cartierDualMap S.f) (by
    rw [← cartierDualMap_comp, S.zero]
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    let f' : S.X₃ →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f
    refine LinearMap.ext fun a => ?_
    change f' ((0 : S.X₁ ⟶ S.X₃).hom a) = 0
    rw [Rep.zero_hom]
    exact map_zero f')

end Exact

section ZMod

theorem nsmul_zmodRep_eq_zero (G : Type*) [Monoid G] (n : ℕ) (x : zmodRep.{u} G n) : n • x = 0 := by
  obtain ⟨z⟩ := x
  apply ULift.ext
  change n • z = 0
  have := AddMonoid.exponent_nsmul_eq_zero z
  rwa [ZMod.exponent] at this

theorem exponent_zmodRep (G : Type*) [Monoid G] (n : ℕ) :
    AddMonoid.exponent (zmodRep.{u} G n) = n := by
  change AddMonoid.exponent (ULift.{u} (ZMod n)) = n
  rw [AddMonoid.exponent_eq_of_addEquiv AddEquiv.ulift, ZMod.exponent]

instance finite_zmodRep (G : Type*) [Monoid G] (n : ℕ) [NeZero n] : Finite (zmodRep.{u} G n) :=
  inferInstanceAs (Finite (ULift.{u} (ZMod n)))

theorem zmodRep_eq_zsmul (G : Type*) [Monoid G] (n : ℕ) (k : ℤ) :
    (ULift.up (k : ZMod n) : zmodRep.{u} G n) = k • (ULift.up 1 : zmodRep.{u} G n) := by
  apply ULift.ext
  change (k : ZMod n) = k • (1 : ZMod n)
  rw [zsmul_one]

variable (K L) in

def cartierDualZModHom (n : ℕ) : cartierDual K L (zmodRep.{u} Gal(L/K) n) ⟶ galRootsOfUnity.{u} K L n :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom (cartierDual K L (zmodRep.{u} Gal(L/K) n))
    (galRootsOfUnity.{u} K L n)).symm
    { toFun := fun f => Additive.ofMul ⟨Additive.toMul (α := Lˣ)
        ((f : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (ULift.up 1)),
        (mem_rootsOfUnity _ _).2 (cartierDual_pow_eq_one (nsmul_zmodRep_eq_zero _ n) _ _)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }, fun σ => by
    refine LinearMap.ext fun f => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl⟩

@[simp]
theorem coe_cartierDualZModHom_hom_apply (n : ℕ)
    (f : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L) :
    ((Additive.toMul ((cartierDualZModHom K L n).hom f) : rootsOfUnity n L) : Lˣ) =
      Additive.toMul (α := Lˣ) (f (ULift.up 1)) :=
  rfl

theorem cartierDualZModHom_bijective (n : ℕ) :
    Function.Bijective (cartierDualZModHom K L n).hom := by
  refine ⟨fun f₀ g₀ h => ?_, fun x => ?_⟩
  · let f : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f₀
    let g : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L := g₀
    have h1 : f (ULift.up 1) = g (ULift.up 1) := by
      have := congrArg (fun y => ((Additive.toMul y : rootsOfUnity n L) : Lˣ)) h
      exact Additive.toMul.injective this
    change f = g
    refine LinearMap.ext fun x => ?_
    obtain ⟨z⟩ := x
    rw [← ZMod.intCast_zmod_cast z, zmodRep_eq_zsmul Gal(L/K) n, map_zsmul, map_zsmul, h1]
  · let ζ : Lˣ := (Additive.toMul x : rootsOfUnity n L)
    have hζ : ζ ^ n = 1 := (mem_rootsOfUnity _ _).1 (Additive.toMul x).2
    let h₀ : ZMod n →+ Additive Lˣ := ZMod.lift n ⟨zmultiplesHom (Additive Lˣ) (Additive.ofMul ζ),
      by
        rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hζ, ofMul_one]⟩
    refine ⟨(uliftIntLinearEquivAddHom (zmodRep.{u} Gal(L/K) n) (galUnits.{u} K L)).symm
      (h₀.comp (AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).toAddMonoidHom), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change Additive.toMul (h₀ 1) = ζ
    rw [← Int.cast_one, ZMod.lift_coe, zmultiplesHom_apply, one_zsmul, toMul_ofMul]

variable (K L) in

def cartierDualZModIso (n : ℕ) : cartierDual K L (zmodRep.{u} Gal(L/K) n) ≅ galRootsOfUnity.{u} K L n :=
  Rep.isoOfBijective (cartierDualZModHom K L n) (cartierDualZModHom_bijective n)

@[simp]
theorem cartierDualZModIso_hom (n : ℕ) : (cartierDualZModIso K L n).hom = cartierDualZModHom K L n :=
  rfl

variable (K L) in

def cartierDualRootsOfUnityIso (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity L n] :
    cartierDual K L (galRootsOfUnity.{u} K L n) ≅ zmodRep.{u} Gal(L/K) n :=
  have : HasEnoughRootsOfUnity L (AddMonoid.exponent (zmodRep.{u} Gal(L/K) n)) := by
    rwa [exponent_zmodRep]
  (cartierDualFunctor K L).mapIso (cartierDualZModIso K L n).op ≪≫
    (cartierBidualityIso K L (zmodRep.{u} Gal(L/K) n)).symm

variable (K L) in

def cartierDualRootsOfUnityIsoOfIsSepClosed [IsSepClosed L] (n : ℕ) (hn : (n : K) ≠ 0) :
    cartierDual K L (galRootsOfUnity.{u} K L n) ≅ zmodRep.{u} Gal(L/K) n :=
  have : NeZero (n : L) := ⟨by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero (algebraMap K L)).2 hn⟩
  have : NeZero n := ⟨fun h => hn (by rw [h, Nat.cast_zero])⟩
  cartierDualRootsOfUnityIso K L n

end ZMod

end GroundTheory.ProfCoh
