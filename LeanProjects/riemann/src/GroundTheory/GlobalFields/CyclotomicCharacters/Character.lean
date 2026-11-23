import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
import GroundTheory.GlobalFields.CyclotomicCharacters.Frobenius

open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract

namespace GroundTheory.Global

namespace Cyclotomic

open GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

instance isAlgClosure_rat : IsAlgClosure ℚ ℚ̄ := by
  let i : Algebra ℚ ℚ̄ := AlgebraicClosure.instAlgebra ℚ (R := ℚ)
  have h : IsAlgClosure ℚ ℚ̄ := inferInstance
  convert h
  exact Subsingleton.elim _ _

section FixingSubgroup

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem mem_fixingSubgroup_adjoin_iff (S : Set E) (σ : Gal(E/F)) :
    σ ∈ (adjoin F S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h x hx => h x (subset_adjoin F S hx), fun h x hx => ?_⟩
  have := adjoin_algHom_ext F (φ₁ := (σ : E →ₐ[F] E).comp (adjoin F S).val)
    (φ₂ := (adjoin F S).val) (fun y hy => h y hy)
  exact congrArg (fun φ : adjoin F S →ₐ[F] E => φ ⟨x, hx⟩) this

end FixingSubgroup

section Fields

noncomputable def rootsOfUnityField (n : ℕ) : IntermediateField ℚ ℚ̄ :=
  adjoin ℚ {x : ℚ̄ | x ^ n = 1}

noncomputable def maxCyclotomic : IntermediateField ℚ ℚ̄ :=
  adjoin ℚ {x : ℚ̄ | ∃ n : ℕ, 0 < n ∧ x ^ n = 1}

theorem maxCyclotomic_eq_iSup : maxCyclotomic = ⨆ n : ℕ+, rootsOfUnityField n := by
  refine le_antisymm (adjoin_le_iff.mpr ?_) (iSup_le fun n => adjoin_le_iff.mpr ?_)
  · rintro x ⟨n, hn, hx⟩
    exact le_iSup (fun n : ℕ+ => rootsOfUnityField n) ⟨n, hn⟩ (subset_adjoin ℚ _ hx)
  · intro x hx
    exact subset_adjoin ℚ _ ⟨n, n.pos, hx⟩

theorem rootsOfUnityField_eq_adjoin {n : ℕ} [NeZero n] {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) :
    rootsOfUnityField n = ℚ⟮ζ⟯ := by
  refine le_antisymm (adjoin_le_iff.mpr fun x hx => ?_) (adjoin_le_iff.mpr ?_)
  · obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (mem_adjoin_simple_self ℚ ζ) i
  · rw [Set.singleton_subset_iff]
    exact subset_adjoin ℚ _ hζ.pow_eq_one

instance (n : ℕ) [NeZero n] : IsCyclotomicExtension {n} ℚ (rootsOfUnityField n) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  rw [rootsOfUnityField_eq_adjoin hζ]
  exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ

instance (n : ℕ) [NeZero n] : NumberField (rootsOfUnityField n) :=
  IsCyclotomicExtension.numberField {n} ℚ _

instance (n : ℕ) [NeZero n] : IsGalois ℚ (rootsOfUnityField n) :=
  IsCyclotomicExtension.isGalois {n} ℚ _

end Fields

section Modular

theorem pow_val_natCast {M : Type*} [Monoid M] {n : ℕ} {t : M} (ht : t ^ n = 1) (k : ℕ) :
    t ^ (k : ZMod n).val = t ^ k := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, ht, one_pow, mul_one]

theorem pow_val_one {M : Type*} [Monoid M] {n : ℕ} {t : M} (ht : t ^ n = 1) :
    t ^ (1 : ZMod n).val = t := by
  have := pow_val_natCast ht 1
  rwa [Nat.cast_one, pow_one] at this

theorem natCard_rootsOfUnity (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n ℚ̄) = n :=
  HasEnoughRootsOfUnity.natCard_rootsOfUnity ℚ̄ n

noncomputable def modCharacter (n : ℕ) [NeZero n] : Gal(ℚ̄/ℚ) →* (ZMod n)ˣ :=
  (modularCyclotomicCharacter ℚ̄ (natCard_rootsOfUnity n)).comp
    (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄)

variable {n : ℕ} [NeZero n]

theorem modCharacter_spec (σ : Gal(ℚ̄/ℚ)) {t : ℚ̄} (ht : t ^ n = 1) :
    σ t = t ^ (modCharacter n σ : ZMod n).val := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp [NeZero.ne n] at ht
  have hmem : Units.mk0 t ht0 ∈ rootsOfUnity n ℚ̄ := by
    rw [mem_rootsOfUnity]; ext; simpa using ht
  exact modularCyclotomicCharacter.spec ℚ̄ (natCard_rootsOfUnity n)
    (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) hmem

theorem modCharacter_unique (σ : Gal(ℚ̄/ℚ)) {c : ZMod n}
    (hc : ∀ t : ℚ̄, t ^ n = 1 → σ t = t ^ c.val) : (modCharacter n σ : ZMod n) = c := by
  refine (modularCyclotomicCharacter.unique ℚ̄ (natCard_rootsOfUnity n)
    (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) fun t ht => ?_).symm
  have ht' : (t : ℚ̄) ^ n = 1 := by
    rw [mem_rootsOfUnity] at ht
    simpa using congrArg Units.val ht
  simpa using hc t ht'

theorem modCharacter_eq_of_apply {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(ℚ̄/ℚ)}
    {c : ZMod n} (h : σ ζ = ζ ^ c.val) : (modCharacter n σ : ZMod n) = c := by
  refine modCharacter_unique σ fun t ht => ?_
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one ht
  rw [map_pow, h, ← pow_mul, ← pow_mul, mul_comm]

theorem castHom_modCharacter {m : ℕ} [NeZero m] (h : m ∣ n) (σ : Gal(ℚ̄/ℚ)) :
    ZMod.castHom h (ZMod m) (modCharacter n σ : ZMod n) = modCharacter m σ := by
  refine (modCharacter_unique σ fun t ht => ?_).symm
  have ht' : t ^ n = 1 := by
    obtain ⟨k, rfl⟩ := h
    rw [pow_mul, ht, one_pow]
  rw [modCharacter_spec σ ht', ZMod.castHom_apply]
  conv_rhs => rw [← ZMod.natCast_zmod_val (modCharacter n σ : ZMod n), ZMod.cast_natCast h,
    pow_val_natCast ht]

theorem modCharacter_eq_one {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(ℚ̄/ℚ)} (h : σ ζ = ζ) :
    modCharacter n σ = 1 := by
  refine Units.ext (modCharacter_eq_of_apply hζ ?_)
  rw [Units.val_one, pow_val_one hζ.pow_eq_one, h]

theorem continuous_modCharacter (n : ℕ) [NeZero n] :
    Continuous fun σ : Gal(ℚ̄/ℚ) => (modCharacter n σ : ZMod n) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have : FiniteDimensional ℚ ℚ⟮ζ⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have hU := (ℚ⟮ζ⟯).fixingSubgroup_isOpen
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • ((ℚ⟮ζ⟯).fixingSubgroup : Set Gal(ℚ̄/ℚ)), ?_, hU.smul σ,
    ⟨1, one_mem _, mul_one σ⟩⟩
  rintro _ ⟨τ, hτ, rfl⟩
  have hτζ : τ ζ = ζ := (mem_fixingSubgroup_iff _ τ).mp hτ ζ (mem_adjoin_simple_self ℚ ζ)
  simp only [Set.mem_preimage, Set.mem_singleton_iff, smul_eq_mul, map_mul,
    modCharacter_eq_one hζ hτζ, mul_one] at hσ ⊢
  exact hσ

theorem exists_modCharacter_eq (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    ∃ σ : Gal(ℚ̄/ℚ), modCharacter n σ = a := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {n} ℚ _
  let τ := (IsCyclotomicExtension.Rat.galEquivZMod n ℚ⟮ζ⟯).symm a
  let ζ' : ℚ⟮ζ⟯ := ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩
  have hζ' : ζ' ^ n = 1 := Subtype.ext hζ.pow_eq_one
  have hτ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n ℚ⟮ζ⟯ τ hζ'
  rw [MulEquiv.apply_symm_apply] at hτ
  refine ⟨τ.liftNormal ℚ̄, Units.ext (modCharacter_eq_of_apply hζ ?_)⟩
  have := AlgEquiv.liftNormal_commutes τ ℚ̄ ζ'
  rw [hτ, map_pow] at this
  exact this

end Modular

section Character

noncomputable def characterToZHat : Gal(ℚ̄/ℚ) →* ℤ̂ where
  toFun σ := ⟨fun n => (modCharacter n σ : ZMod n), mem_profiniteIntegers.mpr
    fun m n h => castHom_modCharacter h σ⟩
  map_one' := by
    ext n
    simp [ProfiniteInteger.proj_apply]
  map_mul' σ τ := by
    ext n
    simp [ProfiniteInteger.proj_apply]

noncomputable def character : Gal(ℚ̄/ℚ) →* ℤ̂ˣ :=
  characterToZHat.toHomUnits

@[simp] theorem proj_character (n : ℕ+) (σ : Gal(ℚ̄/ℚ)) :
    ProfiniteInteger.proj n (character σ : ℤ̂) = (modCharacter n σ : ZMod n) :=
  rfl

theorem character_spec (σ : Gal(ℚ̄/ℚ)) (n : ℕ+) {t : ℚ̄} (ht : t ^ (n : ℕ) = 1) :
    σ t = t ^ (ProfiniteInteger.proj n (character σ : ℤ̂)).val := by
  rw [proj_character]
  exact modCharacter_spec σ ht

theorem eq_character (σ : Gal(ℚ̄/ℚ)) (u : ℤ̂)
    (hu : ∀ (n : ℕ+) (t : ℚ̄), t ^ (n : ℕ) = 1 → σ t = t ^ (ProfiniteInteger.proj n u).val) :
    u = character σ := by
  ext n
  rw [proj_character, modCharacter_unique σ (hu n)]

theorem continuous_character_val : Continuous fun σ : Gal(ℚ̄/ℚ) => (character σ : ℤ̂) := by
  refine continuous_induced_rng.2 (continuous_pi fun n => ?_)
  exact continuous_modCharacter n

theorem continuous_character : Continuous character := by
  rw [Units.continuous_iff]
  refine ⟨continuous_character_val, ?_⟩
  have : (fun σ : Gal(ℚ̄/ℚ) => (((character σ)⁻¹ : ℤ̂ˣ) : ℤ̂)) = fun σ => (character σ⁻¹ : ℤ̂) := by
    funext σ; rw [map_inv]
  rw [this]
  exact continuous_character_val.comp continuous_inv

theorem character_surjective : Function.Surjective character := by
  intro u
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let N : ℕ → ℕ+ := fun k => ⟨(k + 1).factorial, Nat.factorial_pos _⟩
  have hdvd : ∀ {k l : ℕ}, k ≤ l → (N k : ℕ) ∣ N l := fun h =>
    Nat.factorial_dvd_factorial (Nat.succ_le_succ h)
  have hcont : ∀ n : ℕ+, Continuous fun σ : Gal(ℚ̄/ℚ) => ProfiniteInteger.proj n (character σ : ℤ̂) :=
    fun n => (ProfiniteInteger.continuous_proj n).comp continuous_character_val
  let S : ℕ → Set Gal(ℚ̄/ℚ) := fun k =>
    {σ | ProfiniteInteger.proj (N k) (character σ : ℤ̂) = ProfiniteInteger.proj (N k) (u : ℤ̂)}
  have hmono : ∀ k, S (k + 1) ⊆ S k := fun k σ hσ => by
    simp only [S, Set.mem_ofPred_eq] at hσ ⊢
    rw [← ProfiniteInteger.castHom_proj (hdvd k.le_succ) (character σ : ℤ̂), hσ,
      ProfiniteInteger.castHom_proj]
  have hne : ∀ k, (S k).Nonempty := fun k => by
    obtain ⟨σ, hσ⟩ := exists_modCharacter_eq (N k)
      (Units.map (ProfiniteInteger.proj (N k)).toMonoidHom u)
    refine ⟨σ, ?_⟩
    simp only [S, Set.mem_ofPred_eq, proj_character, hσ]
    rfl
  have hclosed : ∀ k, IsClosed (S k) := fun k => isClosed_eq (hcont (N k)) continuous_const
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, Units.ext (ProfiniteInteger.ext fun n => ?_)⟩
  have hn : (n : ℕ) ∣ N n := Nat.dvd_factorial n.pos (Nat.le_succ n)
  rw [← ProfiniteInteger.castHom_proj hn (character σ : ℤ̂), ← ProfiniteInteger.castHom_proj hn,
    show ProfiniteInteger.proj (N n) (character σ : ℤ̂) = _ from hσ n]

theorem character_eq_one_iff (σ : Gal(ℚ̄/ℚ)) :
    character σ = 1 ↔ ∀ x : ℚ̄, (∃ n : ℕ, 0 < n ∧ x ^ n = 1) → σ x = x := by
  constructor
  · rintro h x ⟨n, hn, hx⟩
    obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, hn⟩, rfl⟩
    have := character_spec σ N hx
    rw [h, Units.val_one, map_one, pow_val_one hx] at this
    exact this
  · intro h
    refine Units.ext (eq_character σ 1 fun n t ht => ?_).symm
    rw [map_one, pow_val_one ht]
    exact h t ⟨n, n.pos, ht⟩

theorem ker_character : character.ker = maxCyclotomic.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, character_eq_one_iff, maxCyclotomic, mem_fixingSubgroup_adjoin_iff]
  rfl

theorem fixedField_ker_character : fixedField character.ker = maxCyclotomic := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  rw [ker_character, InfiniteGalois.fixedField_fixingSubgroup]

end Character

section Frobenius

variable (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (rootsOfUnityField m)))
  [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]

theorem isArithFrobAt_restrictNormal_iff (hm : ¬ p ∣ m) (σ : Gal(ℚ̄/ℚ)) :
    IsArithFrobAt ℤ (σ.restrictNormal (rootsOfUnityField m)) P ↔
      (modCharacter m σ : ZMod m) = p := by
  rw [isArithFrobAt_iff p _ P hm]
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ m
    let ζ' : rootsOfUnityField m := ⟨ζ, subset_adjoin ℚ _ hζ.pow_eq_one⟩
    have hζ' : ζ' ^ m = 1 := Subtype.ext hζ.pow_eq_one
    have := congrArg (algebraMap (rootsOfUnityField m) ℚ̄) (h ζ' hζ')
    rw [AlgEquiv.restrictNormal_commutes, map_pow] at this
    refine modCharacter_eq_of_apply hζ ?_
    rw [pow_val_natCast hζ.pow_eq_one]
    exact this
  · intro h x hx
    have hx' : (algebraMap (rootsOfUnityField m) ℚ̄ x) ^ m = 1 := by
      rw [← map_pow, hx, map_one]
    apply (algebraMap (rootsOfUnityField m) ℚ̄).injective
    rw [AlgEquiv.restrictNormal_commutes, map_pow, modCharacter_spec σ hx', h,
      pow_val_natCast hx']

end Frobenius

section Padic

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

def primePowPNat (k : ℕ) : ℕ+ := ⟨ℓ ^ k, pow_pos hℓ.out.pos k⟩

@[simp] theorem coe_primePowPNat (k : ℕ) : (primePowPNat ℓ k : ℕ) = ℓ ^ k := rfl

noncomputable def toPadicInt : ℤ̂ →+* ℤ_[ℓ] :=
  PadicInt.lift (f := fun k => ProfiniteInteger.proj (primePowPNat ℓ k))
    fun k₁ k₂ hk => by
      ext x
      exact ProfiniteInteger.castHom_proj (m := primePowPNat ℓ k₁) (n := primePowPNat ℓ k₂)
        (pow_dvd_pow ℓ hk) x

theorem toZModPow_toPadicInt (k : ℕ) (x : ℤ̂) :
    PadicInt.toZModPow k (toPadicInt ℓ x) =
      ProfiniteInteger.proj (primePowPNat ℓ k) x :=
  RingHom.congr_fun (PadicInt.lift_spec _ k) x

theorem toPadicInt_character (σ : Gal(ℚ̄/ℚ)) :
    toPadicInt ℓ (character σ : ℤ̂) =
      (cyclotomicCharacter ℚ̄ ℓ (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) : ℤ_[ℓ]) := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [toZModPow_toPadicInt, cyclotomicCharacter.toZModPow, proj_character]
  rfl

end Padic

end Cyclotomic

end GroundTheory.Global
