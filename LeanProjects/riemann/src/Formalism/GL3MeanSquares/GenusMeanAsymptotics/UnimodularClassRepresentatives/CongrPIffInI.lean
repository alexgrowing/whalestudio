import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem κι (t : 𝓞 F) : κ (ι t) = algebraMap F K (t : F) := rfl

theorem congrP_iff_inI {k : ℕ} {a b : K} : CongrP 𝔭 k a b ↔ InI 𝔭 k (a - b) := Iff.rfl

theorem inI_int (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {z : 𝓞 K} : InI 𝔭 k (κ z) ↔ z ∈ extP K 𝔭 ^ k := by
  have := integralBasisSpans.congrP_int h𝔭 k z 0
  rw [congrP_iff_inI, map_zero, sub_zero, Ideal.Quotient.eq, sub_zero] at this
  exact this

theorem inI_ι (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {n : 𝓞 F} : InI 𝔭 k (κ (ι n)) ↔ n ∈ 𝔭 ^ k := by
  rw [inI_int h𝔭, mem_pow_iff]

theorem InI.of_mul (hp : 𝔭.IsPrime) {k : ℕ} {t : 𝓞 F} (ht : t ∉ 𝔭) {a : K}
    (h : InI 𝔭 k (κ (ι t) * a)) : InI 𝔭 k a := by
  obtain ⟨u, hu, z, hz, e⟩ := h
  exact ⟨u * t, fun h => (hp.mem_or_mem h).elim hu ht, z, hz, by rw [e, map_mul, map_mul, mul_assoc]⟩

theorem InI.zero (hp : 𝔭.IsPrime) (k : ℕ) : InI (K := K) 𝔭 k 0 :=
  ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one 𝔭).2 h), 0, zero_mem _, by simp⟩

theorem exists_frac (hF : IsFixF K F) {D : K} (hD : star D = D) (h0 : InI 𝔭 0 D) :
    ∃ t δ : 𝓞 F, t ∉ 𝔭 ∧ κ (ι δ) = κ (ι t) * D := by
  obtain ⟨t, ht, z, -, e⟩ := h0
  obtain ⟨δ, hδ⟩ := (conjO_eq_iff_mem_range hF z).1 (by
    apply RingOfIntegers.coe_injective
    show star (κ z) = κ z
    rw [e, star_mul', hD, star_ι hF])
  exact ⟨t, δ, ht, by rw [hδ, e]⟩

theorem InI.divK (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {D : K} (hD : star D = D) (h0 : InI 𝔭 0 D)
    {v : ℕ} (hv : ¬ InI 𝔭 (v + 1) D) {k : ℕ} {a : K} (ha : InI 𝔭 (v + k) a) :
    InI 𝔭 k (D⁻¹ * a) := by
  obtain ⟨t, δ, ht, e⟩ := exists_frac hF hD h0
  have hδv : δ ∉ 𝔭 ^ (v + 1) := fun h =>
    hv (InI.of_mul h𝔭.isPrime ht (by rw [← e]; exact (inI_ι h𝔭).2 h))
  have hδ0 : δ ≠ 0 := fun h => hδv (h ▸ zero_mem _)
  have h1 := InI.div h𝔭 hδ0 hδv ha
  have h2 := InI.mul h𝔭.isPrime (InI.int h𝔭.isPrime (ι t)) h1
  rw [zero_add] at h2
  have ht0 := κι_ne_zero (K := K) (ne_zero_of_notMem ht)
  have hδ0' := κι_ne_zero (K := K) hδ0
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [mul_zero] at e
    exact hδ0' e
  have : D⁻¹ * a = κ (ι t) * ((κ (ι δ))⁻¹ * a) := by
    rw [e]
    field_simp
  rw [this]
  exact h2

theorem inI_of_trace (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {z : K}
    (h : ∀ c : 𝓞 K, InI 𝔭 k (κ c * z + star (κ c * z))) : InI 𝔭 k z := by
  have hp := h𝔭.isPrime
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  set δ := θ - conjO K θ with hδ
  have h1 : InI 𝔭 k (κ δ * z) := by
    have e : κ δ * z = (κ θ * z + star (κ θ * z)) - κ (conjO K θ) * (κ 1 * z + star (κ 1 * z)) := by
      have : κ (conjO K θ) = star (κ θ) := rfl
      rw [hδ, map_sub, this, map_one, one_mul, star_mul']
      ring
    rw [e]
    have h2 := InI.mul hp (InI.int hp (conjO K θ)) (h 1)
    rw [zero_add] at h2
    exact (h θ).sub hp h2
  obtain ⟨ν, hν⟩ := (conjO_eq_iff_mem_range hF (δ * conjO K δ)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  have hνp : ν ∉ 𝔭 := by
    intro hm
    have h3 : δ * conjO K δ ∈ extP K 𝔭 ^ 1 := by rw [← hν]; exact ι_mem_pow (by simpa using hm)
    have h4 : conjO K δ ∈ extP K 𝔭 ^ 1 := mem_of_unit_mul_mem hθ h3
    have h5 : δ ∈ extP K 𝔭 ^ 1 := by
      have := conjO_mem_pow hF 𝔭 1 _ h4
      rwa [conjO_conjO] at this
    have h6 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := mem_of_unit_mul_mem hθ (by rwa [mul_one])
    have h7 := (mem_pow_iff (K := K) 𝔭 1 1).1 (by rwa [map_one])
    rw [pow_one] at h7
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h7)
  apply InI.of_mul hp hνp
  have h8 := InI.mul hp (InI.int hp (conjO K δ)) h1
  rw [zero_add] at h8
  have : κ (ι ν) * z = κ (conjO K δ) * (κ δ * z) := by rw [hν, map_mul]; ring
  rw [this]
  exact h8

end Formalism.HermitianLattices.Ext.L3.Cell
