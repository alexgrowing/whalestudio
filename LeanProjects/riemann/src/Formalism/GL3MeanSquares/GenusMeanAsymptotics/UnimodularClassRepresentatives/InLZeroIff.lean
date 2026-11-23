import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AkCountEqRedCountMul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinitePrimesOfMem

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WCA

open LocalSpans idealPowerSpanBounds localizedQuotients

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

def InI (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : K) : Prop :=
  ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z ∈ extP K 𝔭 ^ k, κ z = κ (ι t) * a

def InL (𝔭 : Ideal (𝓞 F)) (A : Submodule (𝓞 K) V) (k : ℕ) (v : V) : Prop :=
  ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t • v ∈ extP K 𝔭 ^ k • A

variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem κι_ne_zero {t : 𝓞 F} (ht : t ≠ 0) : κ (ι t) ≠ 0 := by
  intro h0
  have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
  exact ht ((FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm))

theorem ne_zero_of_notMem {t : 𝓞 F} (ht : t ∉ 𝔭) : t ≠ 0 := fun h => ht (h ▸ 𝔭.zero_mem)

theorem InI.add (hp : 𝔭.IsPrime) {k : ℕ} {a b : K} (ha : InI 𝔭 k a) (hb : InI 𝔭 k b) :
    InI 𝔭 k (a + b) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  obtain ⟨u, hu, y, hy, f⟩ := hb
  refine ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, ι u * z + ι t * y,
    add_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_left _ _ hy), ?_⟩
  simp only [map_add, map_mul, e, f]
  ring

theorem InI.neg {k : ℕ} {a : K} (ha : InI 𝔭 k a) : InI 𝔭 k (-a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  exact ⟨t, ht, -z, neg_mem hz, by rw [map_neg, e]; ring⟩

theorem InI.sub (hp : 𝔭.IsPrime) {k : ℕ} {a b : K} (ha : InI 𝔭 k a) (hb : InI 𝔭 k b) :
    InI 𝔭 k (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hp hb.neg

theorem InI.mul (hp : 𝔭.IsPrime) {i k : ℕ} {a b : K} (ha : InI 𝔭 i a) (hb : InI 𝔭 k b) :
    InI 𝔭 (i + k) (a * b) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  obtain ⟨u, hu, y, hy, f⟩ := hb
  refine ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, z * y, ?_, ?_⟩
  · rw [pow_add]
    exact Ideal.mul_mem_mul hz hy
  · simp only [map_mul, e, f]
    ring

theorem InI.conj (hF : IsFixF K F) {k : ℕ} {a : K} (ha : InI 𝔭 k a) : InI 𝔭 k (star a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  refine ⟨t, ht, conjO K z, conjO_mem_pow hF 𝔭 k z hz, ?_⟩
  have : κ (conjO K z) = star (κ z) := rfl
  rw [this, e, star_mul', star_ι hF]

theorem InI.mono {i k : ℕ} (hik : k ≤ i) {a : K} (ha : InI 𝔭 i a) : InI 𝔭 k a := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  exact ⟨t, ht, z, Ideal.pow_le_pow_right hik hz, e⟩

theorem InI.int (hp : 𝔭.IsPrime) (z : 𝓞 K) : InI 𝔭 0 (κ z) :=
  ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one 𝔭).2 h), z, by simp, by simp⟩

theorem InI.one (hp : 𝔭.IsPrime) : InI (K := K) 𝔭 0 1 := by
  simpa using InI.int (K := K) hp 1

theorem InL.add (hp : 𝔭.IsPrime) {k : ℕ} {a b : V} (ha : InL 𝔭 A k a) (hb : InL 𝔭 A k b) :
    InL 𝔭 A k (a + b) := by
  obtain ⟨t, ht, e⟩ := ha
  obtain ⟨u, hu, f⟩ := hb
  refine ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, ?_⟩
  rw [smul_add, map_mul]
  refine add_mem ?_ ?_
  · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ e
  · rw [mul_smul]; exact Submodule.smul_mem _ _ f

theorem InL.neg {k : ℕ} {a : V} (ha : InL 𝔭 A k a) : InL 𝔭 A k (-a) := by
  obtain ⟨t, ht, e⟩ := ha
  exact ⟨t, ht, by rw [smul_neg]; exact neg_mem e⟩

theorem InL.sub (hp : 𝔭.IsPrime) {k : ℕ} {a b : V} (ha : InL 𝔭 A k a) (hb : InL 𝔭 A k b) :
    InL 𝔭 A k (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hp hb.neg

theorem InL.mono {i k : ℕ} (hik : k ≤ i) {a : V} (ha : InL 𝔭 A i a) : InL 𝔭 A k a := by
  obtain ⟨t, ht, e⟩ := ha
  exact ⟨t, ht, Submodule.smul_mono_left (Ideal.pow_le_pow_right hik) e⟩

theorem InL.smul (hp : 𝔭.IsPrime) {i k : ℕ} {a : K} {v : V} (ha : InI 𝔭 i a) (hv : InL 𝔭 A k v) :
    InL 𝔭 A (i + k) (a • v) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  obtain ⟨u, hu, f⟩ := hv
  refine ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, ?_⟩
  have : ι (t * u) • a • v = z • (ι u • v) := by
    rw [← algebraMap_smul K (ι (t * u)), ← algebraMap_smul K z, ← algebraMap_smul K (ι u), smul_smul,
      smul_smul, e, map_mul, map_mul]
    congr 1
    ring
  rw [this, pow_add, Submodule.mul_smul]
  exact Submodule.smul_mem_smul hz f

theorem form_mem_right {h : V →ₗ⋆[K] V →ₗ[K] K} (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {J : Ideal (𝓞 K)}
    {l q : V} (hl : l ∈ A) (hq : q ∈ J • A) : ∃ z ∈ J, κ z = h l q := by
  induction hq using Submodule.smul_induction_on' with
  | smul a ha m hm =>
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hA l hl m hm)
    refine ⟨a * r, Ideal.mul_mem_right _ _ ha, ?_⟩
    rw [← algebraMap_smul K a, map_smul, smul_eq_mul, map_mul, hr]
  | add x _ y _ hx hy =>
    obtain ⟨z, hz, e⟩ := hx
    obtain ⟨w, hw, f⟩ := hy
    exact ⟨z + w, add_mem hz hw, by rw [map_add, map_add, e, f]⟩

theorem form_mem (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A)
    {i k : ℕ} {p q : V} (hp : p ∈ extP K 𝔭 ^ i • A) (hq : q ∈ extP K 𝔭 ^ k • A) :
    ∃ z ∈ extP K 𝔭 ^ (i + k), κ z = h p q := by
  induction hp using Submodule.smul_induction_on' with
  | smul a ha m hm =>
    obtain ⟨r, hr, e⟩ := form_mem_right hA hm hq
    refine ⟨conjO K a * r, ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul (conjO_mem_pow hF 𝔭 i a ha) hr
    · rw [← algebraMap_smul K a, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, e]
      rfl
  | add x _ y _ hx hy =>
    obtain ⟨z, hz, e⟩ := hx
    obtain ⟨w, hw, f⟩ := hy
    exact ⟨z + w, add_mem hz hw, by rw [map_add, map_add, LinearMap.add_apply, e, f]⟩

theorem InL.form (hp : 𝔭.IsPrime) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {i k : ℕ} {v w : V} (hv : InL 𝔭 A i v) (hw : InL 𝔭 A k w) :
    InI 𝔭 (i + k) (h v w) := by
  obtain ⟨t, ht, e⟩ := hv
  obtain ⟨u, hu, f⟩ := hw
  obtain ⟨z, hz, g⟩ := form_mem hF hA e f
  exact ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, z, hz, by rw [g, form_smul hF]⟩

theorem exists_div (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1)) :
    ∃ s : 𝓞 F, s ∉ 𝔭 ∧ ∀ k : ℕ, ∀ z ∈ extP K 𝔭 ^ (v + k), ∃ z' ∈ extP K 𝔭 ^ k, ι s * z = ι n * z' := by
  have hc' : Ideal.span {n} ≠ (0 : Ideal (𝓞 F)) := by simpa using hn
  have hu : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]
    exact h𝔭.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hu hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨s, hsb, hsp⟩ := SetLike.not_le_iff_exists.mp hnd
  set m := multiplicity 𝔭 (Ideal.span {n}) with hm
  have hmv : m ≤ v := by
    by_contra hlt
    rw [not_le] at hlt
    apply hv
    have h1 : Ideal.span {n} ≤ 𝔭 ^ m := hb.le.trans Ideal.mul_le_left
    exact Ideal.pow_le_pow_right hlt (h1 (Ideal.mem_span_singleton_self n))
  refine ⟨s, hsp, fun k z hz => ?_⟩
  have h2 : Ideal.span {s} * 𝔭 ^ (v + k) ≤ Ideal.span {n} * 𝔭 ^ k := by
    rw [pow_add, ← mul_assoc]
    refine Ideal.mul_mono_left ?_
    rw [hb, mul_comm]
    exact Ideal.mul_mono (Ideal.pow_le_pow_right hmv) ((Ideal.span_singleton_le_iff_mem _).2 hsb)
  have h3 := Ideal.map_mono (f := ι) h2
  rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_pow, Ideal.map_pow, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_singleton] at h3
  have h4 : ι s * z ∈ Ideal.span {ι n} * extP K 𝔭 ^ k :=
    h3 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz)
  obtain ⟨z', hz', e⟩ := Ideal.mem_span_singleton_mul.1 h4
  exact ⟨z', hz', e.symm⟩

theorem InI.div (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    {a : K} (ha : InI 𝔭 (v + k) a) : InI 𝔭 k ((κ (ι n))⁻¹ * a) := by
  obtain ⟨s, hs, H⟩ := exists_div (K := K) h𝔭 hn hv
  obtain ⟨t, ht, z, hz, e⟩ := ha
  obtain ⟨z', hz', f⟩ := H k z hz
  refine ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, z', hz', ?_⟩
  have hn0 := κι_ne_zero (K := K) hn
  have f' : κ (ι s) * κ z = κ (ι n) * κ z' := by rw [← map_mul, f, map_mul]
  rw [e] at f'
  rw [map_mul, map_mul]
  field_simp
  linear_combination -f'

theorem exists_div_smul {s n : 𝓞 F} {v k : ℕ}
    (H : ∀ z ∈ extP K 𝔭 ^ (v + k), ∃ z' ∈ extP K 𝔭 ^ k, ι s * z = ι n * z') {p : V}
    (hp : p ∈ extP K 𝔭 ^ (v + k) • A) : ∃ p' ∈ extP K 𝔭 ^ k • A, ι s • p = ι n • p' := by
  induction hp using Submodule.smul_induction_on' with
  | smul a ha m hm =>
    obtain ⟨a', ha', e⟩ := H a ha
    exact ⟨a' • m, Submodule.smul_mem_smul ha' hm, by rw [smul_smul, smul_smul, e]⟩
  | add x _ y _ hx hy =>
    obtain ⟨z, hz, e⟩ := hx
    obtain ⟨w, hw, f⟩ := hy
    exact ⟨z + w, add_mem hz hw, by rw [smul_add, smul_add, e, f]⟩

theorem InL.div (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    {w : V} (hw : InL 𝔭 A (v + k) w) : InL 𝔭 A k ((κ (ι n))⁻¹ • w) := by
  obtain ⟨s, hs, H⟩ := exists_div (K := K) h𝔭 hn hv
  obtain ⟨t, ht, e⟩ := hw
  obtain ⟨p', hp', f⟩ := exists_div_smul (H k) e
  refine ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_⟩
  have hn0 := κι_ne_zero (K := K) hn
  have : ι (s * t) • (κ (ι n))⁻¹ • w = p' := by
    have h1 : ι (s * t) • (κ (ι n))⁻¹ • w = (κ (ι n))⁻¹ • (ι s • ι t • w) := by
      rw [map_mul, mul_smul, smul_comm (ι t), smul_comm (ι s)]
    rw [h1, f, ← algebraMap_smul K (ι n), smul_smul, inv_mul_cancel₀ hn0, one_smul]
  rw [this]
  exact hp'

theorem InI.unit (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {ε : K} (hε : InI 𝔭 1 ε) :
    1 + ε ≠ 0 ∧ InI 𝔭 0 ((1 + ε)⁻¹) := by
  obtain ⟨t, ht, z, hz, e⟩ := hε
  set a : 𝓞 K := ι t + z with ha
  have hκa : κ a = κ (ι t) * (1 + ε) := by rw [ha, map_add, e]; ring
  obtain ⟨b, hb⟩ := (conjO_eq_iff_mem_range hF (a * conjO K a)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  have hz' : conjO K z ∈ extP K 𝔭 ^ 1 := conjO_mem_pow hF 𝔭 1 z hz
  have hbp : b ∉ 𝔭 := by
    intro hbp
    have h1 : ι b ∈ extP K 𝔭 ^ 1 := ι_mem_pow (by simpa using hbp)
    have h2 : ι (t * t) ∈ extP K 𝔭 ^ 1 := by
      have : ι (t * t) = ι b - (ι t * conjO K z + z * ι t + z * conjO K z) := by
        rw [hb, ha, map_add, conjO_map hF, map_mul]; ring
      rw [this]
      exact sub_mem h1 (add_mem (add_mem (Ideal.mul_mem_left _ _ hz') (Ideal.mul_mem_right _ _ hz))
        (Ideal.mul_mem_right _ _ hz))
    have h3 : t * t ∈ 𝔭 := by simpa using (mem_pow_iff (K := K) 𝔭 1 (t * t)).1 h2
    exact (h𝔭.isPrime.mem_or_mem h3).elim ht ht
  have hκb : κ (ι b) = κ a * κ (conjO K a) := by rw [hb, map_mul]
  have hne : 1 + ε ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hκa
    rw [hκa, zero_mul] at hκb
    exact κι_ne_zero (K := K) (ne_zero_of_notMem hbp) hκb
  refine ⟨hne, b, hbp, ι t * conjO K a, by simp, ?_⟩
  rw [hκb, hκa, map_mul]
  field_simp

theorem inL_zero_iff (hp : 𝔭.IsPrime) {v : V} : InL 𝔭 A 0 v ↔ v ∈ locF 𝔭 A := by
  rw [mem_locF 𝔭 A v]
  unfold InL
  simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

theorem InL.of_mem (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {v : V} (hv : v ∈ extP K 𝔭 ^ k • locF 𝔭 A) :
    InL 𝔭 A k v := exists_smul_mem h𝔭 A _ hv

theorem InL.mem (hp : 𝔭.IsPrime) {k : ℕ} {v : V} (hv : InL 𝔭 A k v) :
    v ∈ extP K 𝔭 ^ k • locF 𝔭 A := by
  obtain ⟨t, ht, e⟩ := hv
  have ht0 := κι_ne_zero (K := K) (ne_zero_of_notMem ht)
  have key : ∀ p ∈ extP K 𝔭 ^ k • A, (κ (ι t))⁻¹ • p ∈ extP K 𝔭 ^ k • locF 𝔭 A := by
    intro p hp'
    induction hp' using Submodule.smul_induction_on' with
    | smul a ha m hm =>
      rw [smul_comm]
      refine Submodule.smul_mem_smul ha ((mem_locF 𝔭 A _).2 ⟨t, ht, ?_⟩)
      rw [← algebraMap_smul K (ι t), smul_smul, mul_inv_cancel₀ ht0, one_smul]
      exact hm
    | add x _ y _ hx hy =>
      rw [smul_add]
      exact add_mem hx hy
  have := key _ e
  rwa [← algebraMap_smul K (ι t), smul_smul, inv_mul_cancel₀ ht0, one_smul] at this

end Formalism.HermitianLattices.Ext.L3.WCA
