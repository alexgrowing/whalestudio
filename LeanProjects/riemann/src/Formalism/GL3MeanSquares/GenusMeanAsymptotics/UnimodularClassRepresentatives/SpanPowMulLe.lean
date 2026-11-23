import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLocUnif
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def InP (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : K) : Prop :=
  ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z ∈ extP K 𝔭 ^ k, jK z = jK (ι t) * a

theorem congrP_iff_inP (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a b : K) : CongrP 𝔭 k a b ↔ InP 𝔭 k (a - b) := by
  have e : ∀ t : 𝓞 F, jK (ι t) = algebraMap F K (t : F) := fun t => rfl
  simp only [CongrP, InP, e]

theorem jK_inj : Function.Injective (jK) := fun a b hab => RingOfIntegers.ext hab

theorem InP.add {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 k b) : InP 𝔭 k (a + b) := by
  obtain ⟨t₁, ht₁, z₁, hz₁, e₁⟩ := ha
  obtain ⟨t₂, ht₂, z₂, hz₂, e₂⟩ := hb
  refine ⟨t₁ * t₂, fun hm => (h𝔭.mem_or_mem hm).elim ht₁ ht₂, ι t₂ * z₁ + ι t₁ * z₂,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hz₁) (Ideal.mul_mem_left _ _ hz₂), ?_⟩
  simp only [map_add, map_mul, e₁, e₂]
  ring

theorem InP.neg {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : K} (ha : InP 𝔭 k a) : InP 𝔭 k (-a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  exact ⟨t, ht, -z, neg_mem hz, by rw [map_neg, e, mul_neg]⟩

theorem InP.mul {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k l : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 l b) : InP 𝔭 (k + l) (a * b) := by
  obtain ⟨t₁, ht₁, z₁, hz₁, e₁⟩ := ha
  obtain ⟨t₂, ht₂, z₂, hz₂, e₂⟩ := hb
  refine ⟨t₁ * t₂, fun hm => (h𝔭.mem_or_mem hm).elim ht₁ ht₂, z₁ * z₂, ?_, ?_⟩
  · rw [pow_add]
    exact Ideal.mul_mem_mul hz₁ hz₂
  · simp only [map_mul, e₁, e₂]
    ring

theorem InP.mono {𝔭 : Ideal (𝓞 F)} {k l : ℕ} (hkl : l ≤ k) {a : K} (ha : InP 𝔭 k a) : InP 𝔭 l a := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  exact ⟨t, ht, z, Ideal.pow_le_pow_right hkl hz, e⟩

theorem inP_jK {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k : ℕ} {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    InP 𝔭 k (jK z) := ⟨1, (Ideal.ne_top_iff_one _).mp h𝔭.ne_top, z, hz, by rw [map_one, map_one, one_mul]⟩

def SP (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Subring K where
  carrier := {a | InP 𝔭 0 a}
  mul_mem' := fun ha hb => ha.mul hb
  one_mem' := by
    have := inP_jK (K := K) (𝔭 := 𝔭) (k := 0) (z := 1) (by simp)
    rwa [map_one] at this
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := by
    have := inP_jK (K := K) (𝔭 := 𝔭) (k := 0) (z := 0) (by simp)
    rwa [map_zero] at this
  neg_mem' := fun ha => ha.neg

theorem mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K} :
    a ∈ SP K 𝔭 ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z : 𝓞 K, jK z = jK (ι t) * a := by
  show InP 𝔭 0 a ↔ _
  constructor
  · rintro ⟨t, ht, z, -, e⟩
    exact ⟨t, ht, z, e⟩
  · rintro ⟨t, ht, z, e⟩
    exact ⟨t, ht, z, by simp, e⟩

theorem mem_SP_iff_locF {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K} :
    a ∈ SP K 𝔭 ↔ a ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have hp : 𝔭.IsPrime := inferInstance
  have key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s},
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, (Ideal.ne_top_iff_one _).mp hp.ne_top, map_one _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨t₁, ht₁, rfl⟩ := hx
      obtain ⟨t₂, ht₂, rfl⟩ := hy
      exact ⟨t₁ * t₂, fun hm => (hp.mem_or_mem hm).elim ht₁ ht₂, map_mul _ _ _⟩
  change a ∈ SP K 𝔭 ↔ ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s},
    s • a ∈ (1 : Submodule (𝓞 K) K)
  rw [mem_SP]
  constructor
  · rintro ⟨t, ht, z, e⟩
    refine ⟨ι t, Submonoid.subset_closure ⟨t, ht, rfl⟩, ?_⟩
    rw [Submodule.mem_one]
    exact ⟨z, by rw [e, Algebra.smul_def]⟩
  · rintro ⟨s, hs, hsa⟩
    obtain ⟨t, ht, rfl⟩ := key s hs
    rw [Submodule.mem_one] at hsa
    obtain ⟨z, hz⟩ := hsa
    exact ⟨t, ht, z, by rw [hz, Algebra.smul_def]⟩

theorem jK_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (z : 𝓞 K) : jK z ∈ SP K 𝔭 := mem_SP.mpr ⟨1, (Ideal.ne_top_iff_one _).mp (Ideal.IsPrime.ne_top inferInstance), z,
  by rw [map_one, map_one, one_mul]⟩

theorem InP.mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {a : K} (ha : InP 𝔭 k a) : a ∈ SP K 𝔭 := ha.mono (Nat.zero_le _)

theorem InP.conj (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : K} (ha : InP 𝔭 k a) :
    InP 𝔭 k (star a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  have hι : ∀ c : 𝓞 F, conjO K (ι c) = ι c := by
    intro c
    apply RingOfIntegers.ext
    show star (algebraMap F K (c : F)) = algebraMap F K (c : F)
    exact (hF _).mpr ⟨_, rfl⟩
  have hι' : (conjO K).comp (algebraMap (𝓞 F) (𝓞 K)) = algebraMap (𝓞 F) (𝓞 K) := RingHom.ext hι
  refine ⟨t, ht, conjO K z, ?_, ?_⟩
  · have h1 : conjO K z ∈ (extP K 𝔭 ^ k).map (conjO K) := Ideal.mem_map_of_mem _ hz
    rwa [Ideal.map_pow, extP, Ideal.map_map, hι'] at h1
  · have s1 : jK (conjO K z) = star (jK z) := rfl
    have s2 : star (jK (ι t)) = jK (ι t) := (hF _).mpr ⟨_, rfl⟩
    rw [s1, e, star_mul, s2, mul_comm]

theorem exists_unif0 {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ π₀ ∈ 𝔭, π₀ ∉ 𝔭 ^ 2 ∧ ∃ s₀ : 𝓞 F, s₀ ∉ 𝔭 ∧ Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀} := by
  have hne : 𝔭 ≠ ⊥ := fun h0 =>
    RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h0 ▸ h𝔭))
  obtain ⟨π₀, hπ1, hπ2⟩ : ∃ x ∈ 𝔭 ^ 1, x ∉ 𝔭 ^ (1 + 1) := by
    have hlt : 𝔭 ^ (1 + 1) < 𝔭 ^ 1 := Ideal.pow_succ_lt_pow hne 1
    obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx1, hx2⟩
  rw [pow_one] at hπ1
  have hπ2' : π₀ ∉ 𝔭 ^ 2 := hπ2
  obtain ⟨J, hJ⟩ : 𝔭 ∣ Ideal.span {π₀} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ1)
  have hJ𝔭 : ¬ J ≤ 𝔭 := by
    intro hle
    apply hπ2'
    have h3 : Ideal.span {π₀} ≤ 𝔭 ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right hle
    exact h3 (Ideal.subset_span rfl)
  obtain ⟨s₀, hsJ, hs𝔭⟩ := SetLike.not_le_iff_exists.mp hJ𝔭
  refine ⟨π₀, hπ1, hπ2', s₀, hs𝔭, ?_⟩
  rw [hJ, mul_comm 𝔭 J]
  exact Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hsJ)

theorem span_pow_mul_le {𝔭 : Ideal (𝓞 F)} {π₀ s₀ : 𝓞 F}
    (h : Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀}) (k : ℕ) :
    Ideal.span {ι (s₀ ^ k)} * extP K 𝔭 ^ k ≤ Ideal.span {ι (π₀ ^ k)} := by
  have h1 : (Ideal.span {s₀} * 𝔭) ^ k ≤ Ideal.span {π₀} ^ k := Ideal.pow_right_mono h k
  rw [mul_pow, Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h1
  have h2 := Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 K)) h1
  rw [Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.map_pow] at h2
  exact h2

end Formalism.HermitianLattices.Ext.L3.HU
