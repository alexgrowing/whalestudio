import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.UnramifiedRootsOfUnity
import GroundTheory.LocalFields.UnramifiedGalois
import GroundTheory.LocalFields.UnramifiedExistence
import GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
import GroundTheory.LocalFields.AbstractLocalReciprocity.Frobenius
import GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger

section Roots

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem algEquiv_pow_apply_of_apply_eq_pow {L : Type*} [Field L] [Algebra K L] {τ : L ≃ₐ[K] L}
    {x : L} {q : ℕ} (h : τ x = x ^ q) (k : ℕ) : (τ ^ k) x = x ^ q ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h, ← pow_mul, ← pow_succ']

theorem one_lt_card_residueField_pow {n : ℕ} (hn : n ≠ 0) : 1 < Nat.card 𝓀[K] ^ n :=
  Nat.one_lt_pow hn (one_lt_card_residueField K)

theorem exists_frobenius_adjoin {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    ∃ τ : K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯, τ (AdjoinSimple.gen K ζ) = AdjoinSimple.gen K ζ ^ Nat.card 𝓀[K] ∧
      orderOf τ = n ∧ Subgroup.zpowers τ = ⊤ := by
  obtain ⟨hE, hEn⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  let := (finiteExtensionStructure K K⟮ζ⟯).rel
  let := (finiteExtensionStructure K K⟮ζ⟯).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K K⟮ζ⟯
  have := finiteExtensionStructure_valuativeExtension K K⟮ζ⟯
  have h := hE.ramificationIndex_eq_one
  have hζ' : IsPrimitiveRoot (AdjoinSimple.gen K ζ) (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective
  refine ⟨frobenius K K⟮ζ⟯ h, frobenius_apply_of_pow_eq_one h
    (natCast_card_pow_sub_one_ne_zero hn) hζ'.pow_eq_one, ?_, zpowers_frobenius K _ h⟩
  rw [orderOf_frobenius, hEn]

theorem exists_apply_eq_pow_pow {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (σ : Ω ≃ₐ[K] Ω) :
    ∃ a : ℕ, σ ζ = ζ ^ Nat.card 𝓀[K] ^ a := by
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  have := hE.isGalois
  obtain ⟨τ, hτ, -, htop⟩ := exists_frobenius_adjoin hn hζ
  have hmem : σ.restrictNormal K⟮ζ⟯ ∈ Subgroup.zpowers τ := htop ▸ Subgroup.mem_top _
  obtain ⟨a, ha⟩ := mem_powers_iff_mem_zpowers.2 hmem
  refine ⟨a, ?_⟩
  have h1 := AlgEquiv.restrictNormal_commutes σ K⟮ζ⟯ (AdjoinSimple.gen K ζ)
  rw [← ha, algEquiv_pow_apply_of_apply_eq_pow hτ] at h1
  simpa using h1.symm

theorem pow_pow_eq_pow_pow_iff {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (a b : ℕ) :
    ζ ^ Nat.card 𝓀[K] ^ a = ζ ^ Nat.card 𝓀[K] ^ b ↔ a ≡ b [MOD n] := by
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  obtain ⟨τ, hτ, hord, -⟩ := exists_frobenius_adjoin hn hζ
  rw [← hord, ← pow_eq_pow_iff_modEq]
  constructor
  · intro h
    have h' : (τ ^ a) (AdjoinSimple.gen K ζ) = (τ ^ b) (AdjoinSimple.gen K ζ) := by
      rw [algEquiv_pow_apply_of_apply_eq_pow hτ, algEquiv_pow_apply_of_apply_eq_pow hτ]
      exact Subtype.ext (by simpa using h)
    have h1 : (τ ^ b)⁻¹ * τ ^ a = 1 := by
      refine algEquiv_eq_one_of_apply_eq (adjoin_gen_eq_top ζ) ?_
      rw [AlgEquiv.mul_apply, h', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    exact (inv_mul_eq_one.mp h1).symm
  · intro h
    have := congrArg (fun ρ : K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯ ↦ ((ρ (AdjoinSimple.gen K ζ) : K⟮ζ⟯) : Ω)) h
    simpa [algEquiv_pow_apply_of_apply_eq_pow hτ] using this

theorem apply_eq_pow_pow_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) {σ : Ω ≃ₐ[K] Ω} {a : ℕ}
    (ha : σ ζ = ζ ^ Nat.card 𝓀[K] ^ a) {ξ : Ω} (hξ : ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1) :
    σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) := ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]

variable (K Ω) in

class HasUnramifiedRoots : Prop where
  exists_isPrimitiveRoot : ∀ n : ℕ, n ≠ 0 → ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)

instance hasUnramifiedRoots_of_isSepClosed [IsSepClosed Ω] : HasUnramifiedRoots K Ω :=
  ⟨fun _ hn ↦ exists_isPrimitiveRoot_card_pow_sub_one (K := K) hn⟩

variable (K Ω) in

def unramifiedRoots : Set Ω :=
  {ξ | ∃ n : ℕ, n ≠ 0 ∧ ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1}

omit [Algebra K Ω] in

theorem mem_unramifiedRoots_iff {ξ : Ω} :
    ξ ∈ unramifiedRoots K Ω ↔ ∃ m : ℕ, (m : 𝓀[K]) ≠ 0 ∧ ξ ^ m = 1 := by
  constructor
  · rintro ⟨n, hn, hξ⟩
    exact ⟨_, natCast_card_pow_sub_one_ne_zero hn, hξ⟩
  · rintro ⟨m, hm, hξ⟩
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have := Fintype.ofFinite 𝓀[K]
    obtain ⟨p, hp⟩ := CharP.exists 𝓀[K]
    obtain ⟨k, hprime, hcard⟩ := FiniteField.card 𝓀[K] p
    have hpm : ¬ p ∣ m := fun h ↦ hm ((CharP.cast_eq_zero_iff 𝓀[K] p m).2 h)
    have hcop : Nat.Coprime (Nat.card 𝓀[K]) m := by
      rw [Nat.card_eq_fintype_card, hcard]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hprime).2 hpm)
    have hdvd : m ∣ Nat.card 𝓀[K] ^ m.totient - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ Nat.card_pos)).1 (Nat.ModEq.pow_totient hcop).symm
    refine ⟨m.totient, (Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0)).ne', ?_⟩
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hξ, one_pow]

variable (K) in
open Classical in

def unramifiedCoord (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) : ZMod n :=
  if h : ∃ a : ZMod n, ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 →
      σ ξ = ξ ^ Nat.card 𝓀[K] ^ a.val then h.choose else 0

theorem natCast_eq_unramifiedCoord_iff {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (σ : Ω ≃ₐ[K] Ω) (a : ℕ) :
    (a : ZMod n) = unramifiedCoord K σ n ↔ σ ζ = ζ ^ Nat.card 𝓀[K] ^ a := by
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  obtain ⟨a₀, ha₀⟩ := exists_apply_eq_pow_pow hn hζ σ
  have hex : ∃ c : ZMod n, ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 →
      σ ξ = ξ ^ Nat.card 𝓀[K] ^ c.val := by
    refine ⟨a₀, fun ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one hn hζ ?_ hξ⟩
    rw [ha₀, pow_pow_eq_pow_pow_iff hn hζ, ZMod.val_natCast]
    exact (Nat.mod_modEq a₀ n).symm
  have hc : unramifiedCoord K σ n = hex.choose := dif_pos hex
  rw [hc, hex.choose_spec ζ hζ.pow_eq_one, pow_pow_eq_pow_pow_iff hn hζ,
    ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact eq_comm

theorem apply_eq_pow_pow_unramifiedCoord {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (σ : Ω ≃ₐ[K] Ω) :
    σ ζ = ζ ^ Nat.card 𝓀[K] ^ (unramifiedCoord K σ n).val :=
  (natCast_eq_unramifiedCoord_iff hζ σ _).1 (ZMod.natCast_zmod_val _)

variable [HasUnramifiedRoots K Ω]

theorem natCast_eq_unramifiedCoord_iff_forall (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) (a : ℕ) :
    (a : ZMod n) = unramifiedCoord K σ n ↔
      ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 → σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  rw [natCast_eq_unramifiedCoord_iff hζ]
  exact ⟨fun h ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ h hξ, fun h ↦ h ζ hζ.pow_eq_one⟩

theorem unramifiedCoord_one (n : ℕ+) : unramifiedCoord K (1 : Ω ≃ₐ[K] Ω) n = 0 := by
  rw [← (natCast_eq_unramifiedCoord_iff_forall 1 n 0).2 (fun ξ _ ↦ by simp), Nat.cast_zero]

theorem unramifiedCoord_mul (σ τ : Ω ≃ₐ[K] Ω) (n : ℕ+) :
    unramifiedCoord K (σ * τ) n = unramifiedCoord K σ n + unramifiedCoord K τ n := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have h := (natCast_eq_unramifiedCoord_iff hζ (σ * τ)
    ((unramifiedCoord K σ n).val + (unramifiedCoord K τ n).val)).2 (by
      rw [AlgEquiv.mul_apply, apply_eq_pow_pow_unramifiedCoord hζ τ, map_pow,
        apply_eq_pow_pow_unramifiedCoord hζ σ, ← pow_mul, ← pow_add])
  rw [← h, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem castHom_unramifiedCoord (σ : Ω ≃ₐ[K] Ω) {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    ZMod.castHom h (ZMod m) (unramifiedCoord K σ n) = unramifiedCoord K σ m := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  obtain ⟨ξ, hξ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) m m.ne_zero
  have hdvd : Nat.card 𝓀[K] ^ (m : ℕ) - 1 ∣ Nat.card 𝓀[K] ^ (n : ℕ) - 1 := by
    obtain ⟨k, hk⟩ := h
    rw [hk, pow_mul]
    simpa [one_pow] using Nat.sub_dvd_pow_sub_pow (Nat.card 𝓀[K] ^ (m : ℕ)) 1 k
  have hξn : ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hξ.pow_eq_one, one_pow]
  have key := apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ
    (apply_eq_pow_pow_unramifiedCoord hζ σ) hξn
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (natCast_eq_unramifiedCoord_iff hξ σ _).2 key

end Roots

section Degree

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω]

variable (K Ω) in

def unramifiedDegree : (Ω ≃ₐ[K] Ω) →* Multiplicative ℤ̂ where
  toFun σ := Multiplicative.ofAdd ⟨fun n ↦ unramifiedCoord K σ n,
    mem_profiniteIntegers.2 fun _ _ h ↦ castHom_unramifiedCoord σ h⟩
  map_one' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    ext n
    show unramifiedCoord K 1 n = proj n 0
    rw [map_zero, unramifiedCoord_one]
  map_mul' σ τ := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
    congr 1
    ext n
    show unramifiedCoord K (σ * τ) n = proj n (_ + _)
    rw [map_add, unramifiedCoord_mul]
    rfl

theorem proj_toAdd_unramifiedDegree (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) :
    proj n (Multiplicative.toAdd (unramifiedDegree K Ω σ)) = unramifiedCoord K σ n :=
  rfl

theorem multiplicative_ext {x y : Multiplicative ℤ̂}
    (h : ∀ n, proj n (Multiplicative.toAdd x) = proj n (Multiplicative.toAdd y)) : x = y :=
  Multiplicative.toAdd.injective (ProfiniteInteger.ext h)

theorem unramifiedCoord_mul_of_apply_eq (σ : Ω ≃ₐ[K] Ω) {τ : Ω ≃ₐ[K] Ω} {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (hτ : τ ζ = ζ) :
    unramifiedCoord K (σ * τ) n = unramifiedCoord K σ n := by
  have h0 : unramifiedCoord K τ n = 0 := by
    rw [← (natCast_eq_unramifiedCoord_iff hζ τ 0).2 (by simpa using hτ), Nat.cast_zero]
  rw [unramifiedCoord_mul, h0, add_zero]

theorem continuous_unramifiedCoord (n : ℕ+) :
    Continuous fun σ : Ω ≃ₐ[K] Ω ↦ unramifiedCoord K σ n := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have hfin : FiniteDimensional K K⟮ζ⟯ := (isUnramifiedSubextension_adjoin n.ne_zero hζ).1.1
  refine ((IsLocallyConstant.iff_eventually_eq _).2 fun σ ↦ ?_).continuous
  open scoped Pointwise in
  have hU : σ • (K⟮ζ⟯.fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) ∈ nhds σ :=
    (K⟮ζ⟯.fixingSubgroup_isOpen.smul σ).mem_nhds ⟨1, one_mem _, by simp⟩
  filter_upwards [hU] with ρ hρ
  obtain ⟨τ, hτ, rfl⟩ := hρ
  exact unramifiedCoord_mul_of_apply_eq σ hζ
    ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (mem_adjoin_simple_self K ζ))

theorem continuous_unramifiedDegree : Continuous (unramifiedDegree K Ω) :=
  continuous_ofAdd.comp (Continuous.subtype_mk (continuous_pi fun n ↦ continuous_unramifiedCoord n) _)

theorem exists_unramifiedCoord_eq [Normal K Ω] (n : ℕ+) (c : ZMod n) :
    ∃ σ : Ω ≃ₐ[K] Ω, unramifiedCoord K σ n = c := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin n.ne_zero hζ
  have := hE.1
  obtain ⟨τ, hτ, -, -⟩ := exists_frobenius_adjoin n.ne_zero hζ
  refine ⟨(τ ^ c.val).liftNormal Ω, ?_⟩
  have h1 := AlgEquiv.liftNormal_commutes (τ ^ c.val) Ω (AdjoinSimple.gen K ζ)
  rw [algEquiv_pow_apply_of_apply_eq_pow hτ] at h1
  have h2 := (natCast_eq_unramifiedCoord_iff hζ ((τ ^ c.val).liftNormal Ω) c.val).2
    (by simpa using h1)
  rw [← h2, ZMod.natCast_zmod_val]

theorem unramifiedDegree_surjective [IsGalois K Ω] : Function.Surjective (unramifiedDegree K Ω) := by
  intro x
  let N : ℕ → ℕ+ := fun k ↦ ⟨(k + 1).factorial, Nat.factorial_pos _⟩
  let S : ℕ → Set (Ω ≃ₐ[K] Ω) := fun k ↦
    {σ | unramifiedCoord K σ (N k) = proj (N k) (Multiplicative.toAdd x)}
  have hS : ∀ k, IsClosed (S k) := fun k ↦
    isClosed_eq (continuous_unramifiedCoord _) continuous_const
  have hdvd : ∀ k, (N k : ℕ) ∣ N (k + 1) := fun k ↦ Nat.factorial_dvd_factorial (by omega)
  have hmono : ∀ k, S (k + 1) ⊆ S k := by
    intro k σ hσ
    simp only [S, Set.mem_ofPred_eq] at hσ ⊢
    rw [← castHom_unramifiedCoord σ (hdvd k), hσ, castHom_proj]
  have hne : ∀ k, (S k).Nonempty := fun k ↦ exists_unramifiedCoord_eq _ _
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hS 0).isCompact hS
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, multiplicative_ext fun n ↦ ?_⟩
  have hn : (n : ℕ) ∣ N ((n : ℕ) - 1) := by
    show (n : ℕ) ∣ ((n : ℕ) - 1 + 1).factorial
    rw [Nat.sub_add_cancel n.pos]
    exact Nat.dvd_factorial n.pos le_rfl
  rw [proj_toAdd_unramifiedDegree, ← castHom_unramifiedCoord σ hn, hσ _, castHom_proj]

theorem unramifiedDegree_eq_ofAdd_natCast_iff (σ : Ω ≃ₐ[K] Ω) (a : ℕ) :
    unramifiedDegree K Ω σ = Multiplicative.ofAdd (a : ℤ̂) ↔
      ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  constructor
  · rintro h ξ ⟨n, hn, hξ⟩
    have hc : unramifiedCoord K σ ⟨n, Nat.pos_of_ne_zero hn⟩ = a := by
      have := congrArg (fun y ↦ proj ⟨n, Nat.pos_of_ne_zero hn⟩ (Multiplicative.toAdd y)) h
      refine this.trans ?_
      rw [toAdd_ofAdd, map_natCast]
    exact (natCast_eq_unramifiedCoord_iff_forall σ ⟨n, Nat.pos_of_ne_zero hn⟩ a).1 hc.symm ξ hξ
  · intro h
    refine multiplicative_ext fun n ↦ ?_
    rw [proj_toAdd_unramifiedDegree, toAdd_ofAdd, map_natCast]
    exact ((natCast_eq_unramifiedCoord_iff_forall σ n a).2
      fun ξ hξ ↦ h ξ ⟨n, n.ne_zero, hξ⟩).symm

theorem unramifiedDegree_eq_one_iff (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K Ω σ = 1 ↔ ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ := by
  have := unramifiedDegree_eq_ofAdd_natCast_iff σ 0
  simp only [Nat.cast_zero, ofAdd_zero, pow_zero, pow_one] at this
  exact this

theorem unramifiedDegree_eq_ofAdd_one_iff (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K Ω σ = Multiplicative.ofAdd 1 ↔
      ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ ^ Nat.card 𝓀[K] := by
  have := unramifiedDegree_eq_ofAdd_natCast_iff σ 1
  simp only [Nat.cast_one, pow_one] at this
  exact this

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [HasUnramifiedRoots K Ω] in

theorem mem_fixingSubgroup_adjoin_iff {S : Set Ω} {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ (adjoin K S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  rw [← Subgroup.zpowers_le, ← le_iff_le, adjoin_le_iff]
  refine ⟨fun h x hx ↦ (mem_fixedField_iff _ _).1 (h hx) σ (Subgroup.mem_zpowers σ), fun h x hx ↦ ?_⟩
  refine (mem_fixedField_iff _ _).2 fun τ hτ ↦ ?_
  have hσ : σ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := h x hx
  exact (Subgroup.zpowers_le.2 hσ) hτ

end Degree

section MaximalUnramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem pow_sub_one_dvd_pow_sub_one (q : ℕ) {m n : ℕ} (h : m ∣ n) : q ^ m - 1 ∣ q ^ n - 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul]
  simpa [one_pow] using Nat.sub_dvd_pow_sub_pow (q ^ m) 1 k

variable (K Ω) in

def maximalUnramifiedExtension : IntermediateField K Ω :=
  ⨆ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, E.1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem IsUnramifiedSubextension.le_maximalUnramifiedExtension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) : E ≤ maximalUnramifiedExtension K Ω :=
  le_iSup (fun E : {E : IntermediateField K Ω // IsUnramifiedSubextension E} ↦ E.1) ⟨E, hE⟩

theorem adjoin_le_maximalUnramifiedExtension {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : K⟮ζ⟯ ≤ maximalUnramifiedExtension K Ω :=
  (isUnramifiedSubextension_adjoin hn hζ).1.le_maximalUnramifiedExtension

instance normal_maximalUnramifiedExtension : Normal K (maximalUnramifiedExtension K Ω) := by
  have : ∀ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, Normal K E.1 :=
    fun E ↦ E.2.isGalois.to_normal
  unfold maximalUnramifiedExtension
  infer_instance

instance isGalois_maximalUnramifiedExtension [Algebra.IsSeparable K Ω] :
    IsGalois K (maximalUnramifiedExtension K Ω) :=
  have := Algebra.isSeparable_tower_bot_of_isSeparable K (maximalUnramifiedExtension K Ω) Ω
  isGalois_iff.2 ⟨this, inferInstance⟩

variable [HasUnramifiedRoots K Ω]

theorem IsUnramifiedSubextension.le_adjoin {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hn : n ≠ 0) (hdvd : Module.finrank K E ∣ n) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E ≤ K⟮ζ⟯ := by
  have := hE.1
  have hm : Module.finrank K E ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨ξ, hξ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hm
  rw [hE.eq_adjoin rfl hm hξ, adjoin_simple_le_iff]
  have hξn : ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1 := by
    obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hdvd
    rw [hc, pow_mul, hξ.pow_eq_one, one_pow]
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) :=
    ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξn
  exact pow_mem (mem_adjoin_simple_self K ζ) i

theorem directed_isUnramifiedSubextension :
    Directed (· ≤ ·) (fun E : {E : IntermediateField K Ω // IsUnramifiedSubextension E} ↦ E.1) := by
  rintro ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
  have := h₁.1
  have := h₂.1
  have hn : Module.finrank K E₁ * Module.finrank K E₂ ≠ 0 :=
    mul_ne_zero Module.finrank_pos.ne' Module.finrank_pos.ne'
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn
  exact ⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin hn hζ).1⟩,
    h₁.le_adjoin hn (dvd_mul_right _ _) hζ, h₂.le_adjoin hn (dvd_mul_left _ _) hζ⟩

theorem coe_maximalUnramifiedExtension : (maximalUnramifiedExtension K Ω : Set Ω) =
    ⋃ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, (E.1 : Set Ω) := by
  have : Nonempty {E : IntermediateField K Ω // IsUnramifiedSubextension E} := by
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) 1 one_ne_zero
    exact ⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin one_ne_zero hζ).1⟩⟩
  exact coe_iSup_of_directed directed_isUnramifiedSubextension

theorem mem_maximalUnramifiedExtension_iff {x : Ω} :
    x ∈ maximalUnramifiedExtension K Ω ↔ ∃ E : IntermediateField K Ω, IsUnramifiedSubextension E ∧ x ∈ E := by
  rw [← SetLike.mem_coe, coe_maximalUnramifiedExtension, Set.mem_iUnion]
  exact ⟨fun ⟨E, h⟩ ↦ ⟨E.1, E.2, h⟩, fun ⟨E, hE, h⟩ ↦ ⟨⟨E, hE⟩, h⟩⟩

theorem maximalUnramifiedExtension_eq_adjoin :
    maximalUnramifiedExtension K Ω = adjoin K (unramifiedRoots K Ω) := by
  apply le_antisymm
  · refine iSup_le fun E ↦ ?_
    have := E.2.1
    have hn : Module.finrank K E.1 ≠ 0 := Module.finrank_pos.ne'
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn
    rw [E.2.eq_adjoin rfl hn hζ, adjoin_simple_le_iff]
    exact subset_adjoin K _ ⟨_, hn, hζ.pow_eq_one⟩
  · rw [adjoin_le_iff]
    rintro ξ ⟨n, hn, hξ⟩
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
    have : NeZero (Nat.card 𝓀[K] ^ n - 1) :=
      ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact adjoin_le_maximalUnramifiedExtension hn hζ (pow_mem (mem_adjoin_simple_self K ζ) i)

theorem unramifiedRoots_subset_maximalUnramifiedExtension :
    unramifiedRoots K Ω ⊆ maximalUnramifiedExtension K Ω := by
  rw [maximalUnramifiedExtension_eq_adjoin]
  exact subset_adjoin K _

instance hasUnramifiedRoots_maximalUnramifiedExtension : HasUnramifiedRoots K (maximalUnramifiedExtension K Ω) :=
  ⟨fun n hn ↦ by
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
    exact ⟨⟨ζ, unramifiedRoots_subset_maximalUnramifiedExtension ⟨n, hn, hζ.pow_eq_one⟩⟩,
      hζ.of_map_of_injective (f := (maximalUnramifiedExtension K Ω).val) Subtype.val_injective⟩⟩

theorem ker_unramifiedDegree :
    (unramifiedDegree K Ω).ker = (maximalUnramifiedExtension K Ω).fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, unramifiedDegree_eq_one_iff, maximalUnramifiedExtension_eq_adjoin,
    mem_fixingSubgroup_adjoin_iff]

theorem unramifiedDegree_restrictNormal (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (σ.restrictNormal (maximalUnramifiedExtension K Ω)) =
      unramifiedDegree K Ω σ := by
  refine multiplicative_ext fun n ↦ ?_
  rw [proj_toAdd_unramifiedDegree, proj_toAdd_unramifiedDegree]
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have hζE : ζ ∈ maximalUnramifiedExtension K Ω :=
    unramifiedRoots_subset_maximalUnramifiedExtension ⟨n, n.ne_zero, hζ.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : maximalUnramifiedExtension K Ω) (Nat.card 𝓀[K] ^ (n : ℕ) - 1) :=
    hζ.of_map_of_injective (f := (maximalUnramifiedExtension K Ω).val) Subtype.val_injective
  rw [← (natCast_eq_unramifiedCoord_iff hζ' _ (unramifiedCoord K σ n).val).2 ?_,
    ZMod.natCast_zmod_val]
  apply Subtype.ext
  have h1 := AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension K Ω) ⟨ζ, hζE⟩
  simp only [IntermediateField.algebraMap_apply] at h1
  rw [h1]
  simpa using apply_eq_pow_pow_unramifiedCoord hζ σ

variable [IsGalois K Ω]

theorem unramifiedDegree_maximalUnramifiedExtension_surjective :
    Function.Surjective (unramifiedDegree K (maximalUnramifiedExtension K Ω)) := by
  intro x
  obtain ⟨σ, rfl⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) x
  exact ⟨_, unramifiedDegree_restrictNormal σ⟩

theorem unramifiedDegree_maximalUnramifiedExtension_injective :
    Function.Injective (unramifiedDegree K (maximalUnramifiedExtension K Ω)) := by
  rw [injective_iff_map_eq_one]
  intro ρ hρ
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
    (K₁ := maximalUnramifiedExtension K Ω) (E := Ω) ρ
  have hσ : σ ∈ (unramifiedDegree K Ω).ker := by
    rw [MonoidHom.mem_ker, ← unramifiedDegree_restrictNormal]
    exact hρ
  rw [ker_unramifiedDegree, ← IntermediateField.restrictNormalHom_ker] at hσ
  exact MonoidHom.mem_ker.1 hσ

variable (K Ω) in

def maximalUnramifiedExtensionGaloisEquiv :
    (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) ≃ₜ* Multiplicative ℤ̂ :=
  let e : (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) ≃* Multiplicative ℤ̂ :=
    MulEquiv.ofBijective (unramifiedDegree K (maximalUnramifiedExtension K Ω))
      ⟨unramifiedDegree_maximalUnramifiedExtension_injective, unramifiedDegree_maximalUnramifiedExtension_surjective⟩
  { e with
    continuous_toFun := continuous_unramifiedDegree
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) continuous_unramifiedDegree).symm.continuous }

@[simp]
theorem maximalUnramifiedExtensionGaloisEquiv_apply (ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :
    maximalUnramifiedExtensionGaloisEquiv K Ω ρ = unramifiedDegree K (maximalUnramifiedExtension K Ω) ρ :=
  rfl

variable (K Ω) in

def maximalUnramifiedExtensionFrobenius : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω :=
  (maximalUnramifiedExtensionGaloisEquiv K Ω).symm (Multiplicative.ofAdd 1)

theorem unramifiedDegree_maximalUnramifiedExtensionFrobenius :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (maximalUnramifiedExtensionFrobenius K Ω) =
      Multiplicative.ofAdd 1 :=
  (maximalUnramifiedExtensionGaloisEquiv K Ω).apply_symm_apply _

theorem eq_maximalUnramifiedExtensionFrobenius_iff (ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :
    ρ = maximalUnramifiedExtensionFrobenius K Ω ↔
      ∀ ξ ∈ unramifiedRoots K (maximalUnramifiedExtension K Ω), ρ ξ = ξ ^ Nat.card 𝓀[K] := by
  rw [← unramifiedDegree_eq_ofAdd_one_iff,
    ← unramifiedDegree_maximalUnramifiedExtensionFrobenius (K := K) (Ω := Ω)]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm

theorem maximalUnramifiedExtensionFrobenius_apply {ξ : maximalUnramifiedExtension K Ω}
    (hξ : ξ ∈ unramifiedRoots K (maximalUnramifiedExtension K Ω)) :
    maximalUnramifiedExtensionFrobenius K Ω ξ = ξ ^ Nat.card 𝓀[K] :=
  (eq_maximalUnramifiedExtensionFrobenius_iff _).1 rfl ξ hξ

theorem maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one {ξ : maximalUnramifiedExtension K Ω} {m : ℕ}
    (hm : (m : 𝓀[K]) ≠ 0) (hξ : ξ ^ m = 1) :
    maximalUnramifiedExtensionFrobenius K Ω ξ = ξ ^ Nat.card 𝓀[K] :=
  maximalUnramifiedExtensionFrobenius_apply (mem_unramifiedRoots_iff.2 ⟨m, hm, hξ⟩)

theorem restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (σ : Ω ≃ₐ[K] Ω) :
    σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ↔
      unramifiedDegree K Ω σ = Multiplicative.ofAdd 1 := by
  rw [← unramifiedDegree_restrictNormal, ← unramifiedDegree_maximalUnramifiedExtensionFrobenius (K := K) (Ω := Ω)]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω] in

theorem dense_zpowers_ofAdd_one :
    Dense (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) := by
  have h : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) =
      Multiplicative.ofAdd '' Set.range (Int.cast : ℤ → ℤ̂) := by
    ext y
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, ⟨k, rfl⟩, by rw [← ofAdd_zsmul, zsmul_one]⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by rw [← ofAdd_zsmul, zsmul_one]⟩
  rw [h]
  exact Multiplicative.ofAdd.surjective.denseRange.dense_image continuous_ofAdd denseRange_intCast

theorem dense_zpowers_maximalUnramifiedExtensionFrobenius :
    Dense (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :
      Set (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω)) := by
  have h : (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :
      Set (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω)) =
      (maximalUnramifiedExtensionGaloisEquiv K Ω).symm ''
        (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) := by
    ext ρ
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, by rw [map_zpow]; rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by rw [map_zpow]; rfl⟩
  rw [h]
  exact (maximalUnramifiedExtensionGaloisEquiv K Ω).symm.surjective.denseRange.dense_image
    (maximalUnramifiedExtensionGaloisEquiv K Ω).symm.continuous dense_zpowers_ofAdd_one

theorem topologicalClosure_zpowers_maximalUnramifiedExtensionFrobenius :
    (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω)).topologicalClosure = ⊤ :=
  SetLike.coe_injective (by
    rw [Subgroup.topologicalClosure_coe, dense_zpowers_maximalUnramifiedExtensionFrobenius.closure_eq,
      Subgroup.coe_top])

end MaximalUnramified

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

instance hasUnramifiedRoots_of_isSepClosure [IsSepClosure K Ω] : HasUnramifiedRoots K Ω :=
  have := IsSepClosure.sep_closed K (K := Ω)
  inferInstance

theorem unramifiedDegree_spec [IsSepClosure K Ω] :
    Continuous (unramifiedDegree K Ω) ∧ Function.Surjective (unramifiedDegree K Ω) ∧
      (unramifiedDegree K Ω).ker = (maximalUnramifiedExtension K Ω).fixingSubgroup :=
  ⟨continuous_unramifiedDegree, unramifiedDegree_surjective, ker_unramifiedDegree⟩

end SeparableClosure

section Finite

section Card

variable (K M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M]

theorem card_residueField_eq_pow_residueDegree :
    Nat.card 𝓀[M] = Nat.card 𝓀[K] ^ residueDegree K M := by
  have := Fintype.ofFinite 𝓀[K]
  have := Fintype.ofFinite 𝓀[M]
  rw [residueDegree_eq_finrank, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[M])]

end Card

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

theorem unramifiedCoord_fixingSubgroup (σ : L.fixingSubgroup) (n : ℕ+) :
    unramifiedCoord K (σ : Ω ≃ₐ[K] Ω) n =
      (residueDegree K L : ZMod n) * unramifiedCoord L (fixingSubgroupEquiv L σ) n := by
  have hQ := card_residueField_eq_pow_residueDegree K L
  have key : ((residueDegree K L * (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val : ℕ) :
      ZMod n) = unramifiedCoord K (σ : Ω ≃ₐ[K] Ω) n := by
    rw [natCast_eq_unramifiedCoord_iff_forall]
    intro ξ hξ
    have hξ' : ξ ^ (Nat.card 𝓀[L] ^ (n : ℕ) - 1) = 1 := by
      rw [hQ, ← pow_mul]
      obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K])
        (dvd_mul_left (n : ℕ) (residueDegree K L))
      rw [hc, pow_mul, hξ, one_pow]
    have h := (natCast_eq_unramifiedCoord_iff_forall (K := L) (fixingSubgroupEquiv L σ) n
      (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val).1 (ZMod.natCast_zmod_val _) ξ hξ'
    rw [hQ, ← pow_mul] at h
    exact h
  rw [← key, Nat.cast_mul, ZMod.natCast_zmod_val]

theorem unramifiedDegree_fixingSubgroup (σ : L.fixingSubgroup) :
    unramifiedDegree K Ω σ = unramifiedDegree L Ω (fixingSubgroupEquiv L σ) ^ residueDegree K L := by
  refine multiplicative_ext fun n ↦ ?_
  rw [proj_toAdd_unramifiedDegree, toAdd_pow, map_nsmul, proj_toAdd_unramifiedDegree, nsmul_eq_mul,
    unramifiedCoord_fixingSubgroup]

variable [IsGalois K Ω]

theorem map_unramifiedDegree_fixingSubgroup :
    L.fixingSubgroup.map (unramifiedDegree K Ω) =
      (powMonoidHom (residueDegree K L) : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range := by
  have := IsGalois.tower_top_of_isGalois K L Ω
  ext x
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (unramifiedDegree_fixingSubgroup L ⟨σ, hσ⟩).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨τ, rfl⟩ := unramifiedDegree_surjective (K := L) (Ω := Ω) y
    obtain ⟨σ, rfl⟩ := (fixingSubgroupEquiv L).surjective τ
    exact ⟨σ, σ.2, (unramifiedDegree_fixingSubgroup L σ)⟩

theorem inertiaDegree_unramifiedDegree_fixingSubgroup :
    inertiaDegree (unramifiedDegree K Ω) L.fixingSubgroup = residueDegree K L := by
  rw [inertiaDegree, map_unramifiedDegree_fixingSubgroup,
    ProfiniteInteger.index_range_powMonoidHom (residueDegree_pos K L).ne']

end Finite

end GroundTheory.LocalField
