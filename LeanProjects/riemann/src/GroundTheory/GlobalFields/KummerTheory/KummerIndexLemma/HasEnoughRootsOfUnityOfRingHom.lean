import Mathlib
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import GroundTheory.GlobalFields.IdeleGroups.IndexProductFormula
import GroundTheory.ProfiniteCohomology.KummerBasic

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero

namespace KummerIndex

theorem hasEnoughRootsOfUnity_of_ringHom {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity F n] : HasEnoughRootsOfUnity E n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
  exact ⟨⟨f ζ, hζ.map_of_injective f.injective⟩, rootsOfUnity.isCyclic E n⟩

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev localUnits : Subgroup (v.adicCompletion K)ˣ :=
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units

variable {v} in

theorem mem_localUnits_iff {x : (v.adicCompletion K)ˣ} :
    x ∈ localUnits v ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  change (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ _
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hx)).1 h2)
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩

theorem units_map_mem_localUnits {a : Kˣ} (ha : v.valuation K (a : K) = 1) :
    Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a ∈ localUnits v := by
  rw [mem_localUnits_iff, Units.coe_map]
  change Valued.v ((a : K) : v.adicCompletion K) = 1
  rw [valuedAdicCompletion_eq_valuation', ha]

def localClass (p : ℕ) : Kˣ →* UnitsModPow (v.adicCompletion K) p :=
  (QuotientGroup.mk' (unitsPow (v.adicCompletion K) p)).comp
    (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K))

theorem ker_localClass (p : ℕ) :
    (localClass v p).ker = unitsPowIn K p (v.adicCompletion K) := by
  rw [localClass, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rfl

def localUnitClasses (p : ℕ) : Subgroup (UnitsModPow (v.adicCompletion K) p) :=
  (localUnits v).map (QuotientGroup.mk' (unitsPow (v.adicCompletion K) p))

theorem localClass_mem_localUnitClasses (p : ℕ) {a : Kˣ} (ha : v.valuation K (a : K) = 1) :
    localClass v p a ∈ localUnitClasses v p :=
  Subgroup.mem_map_of_mem _ (units_map_mem_localUnits v ha)

def ordMod (p : ℕ) : (v.adicCompletion K)ˣ →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p))
  map_one' := by simp
  map_mul' x y := by
    have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
    rw [Units.val_mul, map_mul, log_mul hx hy, ← ofAdd_add]
    push_cast
    ring_nf

theorem exists_uniformizer_unit :
    ∃ π : (v.adicCompletion K)ˣ, Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := valued_adicCompletion_surjective (v := v) (K := K) (exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact exp_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

theorem ordMod_surjective (p : ℕ) [NeZero p] : Function.Surjective (ordMod v p) := by
  obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
  intro z
  refine ⟨π ^ (Multiplicative.toAdd z).val, ?_⟩
  change Multiplicative.ofAdd (((-log (Valued.v ((π ^ (Multiplicative.toAdd z).val :
    (v.adicCompletion K)ˣ) : v.adicCompletion K)) : ℤ) : ZMod p)) = z
  rw [Units.val_pow_eq_pow_val, map_pow, hπ, ← exp_nsmul, log_exp]
  simp only [smul_neg, nsmul_eq_mul, mul_one, neg_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
  rfl

theorem ker_ordMod (p : ℕ) [NeZero p] :
    (ordMod v p).ker = localUnits v ⊔ unitsPow (v.adicCompletion K) p := by
  apply le_antisymm
  · intro x hx
    have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    rw [MonoidHom.mem_ker] at hx
    change Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      at hx
    rw [ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
    have hu : x * ((π ^ k) ^ p)⁻¹ ∈ localUnits v := by
      rw [mem_localUnits_iff, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
        Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_pow, map_zpow₀, hπ,
        ← exp_zsmul, ← exp_nsmul, ← exp_log hx0]
      rw [← exp_neg, ← exp_add]
      have : -(-log (Valued.v (x : v.adicCompletion K))) = (p : ℤ) * (-k) := by
        rw [hk]; ring
      rw [exp_eq_one]
      rw [neg_neg] at this
      rw [this]
      simp only [smul_eq_mul, nsmul_eq_mul]
      ring
    have hx' : x = (x * ((π ^ k) ^ p)⁻¹) * (π ^ k) ^ p := by group
    rw [hx']
    exact Subgroup.mul_mem_sup hu ⟨π ^ k, rfl⟩
  · rw [sup_le_iff]
    constructor
    · intro x hx
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      rw [(mem_localUnits_iff).1 hx, log_one]
      simp
    · rintro _ ⟨b, rfl⟩
      have hb : Valued.v (b : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 b.ne_zero
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (((-log (Valued.v (((b ^ p : (v.adicCompletion K)ˣ)) :
        v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, log_pow]
      simp

theorem index_localUnits_sup_unitsPow (p : ℕ) [NeZero p] :
    (localUnits v ⊔ unitsPow (v.adicCompletion K) p).index = p := by
  rw [← ker_ordMod, Subgroup.index_ker, (ordMod v p).range_eq_top_of_surjective
    (ordMod_surjective v p), Subgroup.card_top, Nat.card_eq_fintype_card]
  simp

theorem index_unitsPow (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) :
    (unitsPow (v.adicCompletion K) p).index = p ^ 2 := by
  have := hasEnoughRootsOfUnity_of_ringHom (algebraMap K (v.adicCompletion K)) p
  have h := index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity v (n := p)
  rw [norm_natCast_adicCompletion_eq_one hv, div_one] at h
  exact_mod_cast h

theorem natCard_localUnitClasses (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) : Nat.card (localUnitClasses v p) = p := by
  have hidx : (localUnitClasses v p).index = p := by
    rw [localUnitClasses, Subgroup.index_map, QuotientGroup.ker_mk',
      (QuotientGroup.mk' _).range_eq_top_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.index_top, mul_one, index_localUnits_sup_unitsPow]
  have hcard : Nat.card (UnitsModPow (v.adicCompletion K) p) = p ^ 2 :=
    index_unitsPow v p hv
  have h := Subgroup.card_mul_index (localUnitClasses v p)
  rw [hidx, hcard, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_right (NeZero.pos p) h

theorem exists_mul_zpow_inv_mem_unitsPow (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) {a x : (v.adicCompletion K)ˣ} (ha : a ∈ localUnits v)
    (hx : x ∈ localUnits v) (hap : a ∉ unitsPow (v.adicCompletion K) p) :
    ∃ k : ℤ, x * (a ^ k)⁻¹ ∈ unitsPow (v.adicCompletion K) p := by
  let g : localUnitClasses v p := ⟨QuotientGroup.mk' _ a, Subgroup.mem_map_of_mem _ ha⟩
  let g' : localUnitClasses v p := ⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ hx⟩
  have hg : g ≠ 1 := by
    intro h
    apply hap
    have h' : QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) a = 1 := congrArg Subtype.val h
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_prime_card (natCard_localUnitClasses v p hv) hg (g' := g'))
  refine ⟨k, ?_⟩
  have h' : QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) a ^ k =
      QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) x := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow] at this
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  change QuotientGroup.mk' _ x * (QuotientGroup.mk' _ a ^ k)⁻¹ = 1
  rw [h']
  exact mul_inv_cancel _

end KummerIndex

end GroundTheory.Global
