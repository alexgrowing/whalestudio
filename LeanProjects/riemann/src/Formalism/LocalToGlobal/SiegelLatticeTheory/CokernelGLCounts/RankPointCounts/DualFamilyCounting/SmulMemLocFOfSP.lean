import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.UnitPairSolutions

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem inP_alg_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a : 𝓞 F) :
    InP 𝔭 k (algebraMap F K (a : F)) ↔ a ∈ 𝔭 ^ k := by
  haveI := h𝔭.isPrime
  rw [← idealPowerSpanBounds.mem_pow_iff (K := K)]
  constructor
  · rintro ⟨t, ht, z, hz, hzeq⟩
    have hz' : z = algebraMap (𝓞 F) (𝓞 K) t * algebraMap (𝓞 F) (𝓞 K) a := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [hzeq, map_mul]
      rfl
    refine idealPowerSpanBounds.mem_of_mul_mem h𝔭 (v := 0) (d := t) (by simpa using ht) ?_
    rw [zero_add, ← hz']
    exact hz
  · intro ha
    exact inP_jK ha

private theorem mem_pow_vF_of_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) :
    a ∈ 𝔭 ^ vF 𝔭 a ∧ a ∉ 𝔭 ^ (vF 𝔭 a + 1) := by
  have hex : ∃ j, a ∉ 𝔭 ^ j := by
    by_contra h
    push_neg at h
    have hi : a ∈ ⨅ i : ℕ, 𝔭 ^ i := (Submodule.mem_iInf _).mpr h
    rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top] at hi
    exact ha ((Submodule.mem_bot _).mp hi)
  obtain ⟨j, hj⟩ := hex
  have hbdd : BddAbove {e : ℕ | a ∈ 𝔭 ^ e} := by
    refine ⟨j, fun e he => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hj (Ideal.pow_le_pow_right hlt.le he)
  refine ⟨Nat.sSup_mem ⟨0, by simp⟩ hbdd, fun h => ?_⟩
  have hc := le_csSup hbdd (show vF 𝔭 a + 1 ∈ {e : ℕ | a ∈ 𝔭 ^ e} from h)
  change vF 𝔭 a + 1 ≤ vF 𝔭 a at hc
  omega

theorem unit_part (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {a : 𝓞 F} (ha : a ≠ 0) :
    (algebraMap F K (a : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a ∈ SP K 𝔭 := by
  haveI := h𝔭.isPrime
  obtain ⟨hmem, hnot⟩ := mem_pow_vF_of_ne_zero h𝔭 ha
  have hle : Ideal.span {s₀ ^ vF 𝔭 a} * 𝔭 ^ vF 𝔭 a ≤ Ideal.span {π ^ vF 𝔭 a} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, ← mul_pow]
    exact Ideal.pow_right_mono hu.le _
  have hsa : s₀ ^ vF 𝔭 a * a ∈ Ideal.span {π ^ vF 𝔭 a} :=
    hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hmem)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hsa
  have hne : 𝔭 ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨π, hu.mem, hu.ne_zero⟩
  have hbnot : b ∉ 𝔭 := by
    intro hb𝔭
    have h1 : s₀ ^ vF 𝔭 a * a ∈ 𝔭 ^ (0 + vF 𝔭 a + 1) := by
      rw [← hb, zero_add, pow_succ, mul_comm b]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hu.mem _) hb𝔭
    refine idealPowerSpanBounds.mul_notMem h𝔭.isPrime hne ?_ hnot h1
    rw [zero_add, pow_one]
    exact fun h => hu.s_notMem (h𝔭.isPrime.mem_of_pow_mem _ h)
  have hbK : algebraMap F K (b : F) * algebraMap F K (π : F) ^ vF 𝔭 a =
      algebraMap F K (s₀ : F) ^ vF 𝔭 a * algebraMap F K (a : F) := by
    have := congrArg (fun x : 𝓞 F => algebraMap F K (x : F)) hb
    simpa [map_mul, map_pow] using this
  have haK : algebraMap F K (a : F) ≠ 0 := by simpa using ha
  refine mem_SP.mpr ⟨b, hbnot, algebraMap (𝓞 F) (𝓞 K) (s₀ ^ vF 𝔭 a), ?_⟩
  show algebraMap F K ((s₀ ^ vF 𝔭 a : 𝓞 F) : F) =
    algebraMap F K (b : F) * ((algebraMap F K (a : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a)
  have hc : ((s₀ ^ vF 𝔭 a : 𝓞 F) : F) = (s₀ : F) ^ vF 𝔭 a := by simp
  rw [hc, map_pow, ← mul_assoc, mul_comm (algebraMap F K (b : F)), mul_assoc, hbK]
  field_simp

private theorem exists_unit_mul_pow_eq_pow_mul_of_isUnif0 {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π s₀ : 𝓞 F}
    (hu : IsUnif0 𝔭 π s₀) {n : ℕ} {C : 𝓞 F} (hC : C ∈ 𝔭 ^ n) (hC' : C ∉ 𝔭 ^ (n + 1)) :
    ∃ b ∉ 𝔭, b * π ^ n = s₀ ^ n * C := by
  have hle : Ideal.span {s₀ ^ n} * 𝔭 ^ n ≤ Ideal.span {π ^ n} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, ← mul_pow]
    exact Ideal.pow_right_mono hu.le _
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp
    (hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hC))
  refine ⟨b, fun hb𝔭 => ?_, hb⟩
  have hne : 𝔭 ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨π, hu.mem, hu.ne_zero⟩
  have h1 : s₀ ^ n * C ∈ 𝔭 ^ (0 + n + 1) := by
    rw [← hb, zero_add, pow_succ, mul_comm b]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hu.mem _) hb𝔭
  refine idealPowerSpanBounds.mul_notMem h𝔭.isPrime hne ?_ hC' h1
  rw [zero_add, pow_one]
  exact fun h => hu.s_notMem (h𝔭.isPrime.mem_of_pow_mem _ h)

theorem unit_part_c (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {a : 𝓞 F} (ha : a ≠ 0) (he : vF 𝔭 a ≠ 0) {c : F}
    (hac : InP 𝔭 (2 * vF 𝔭 a) (algebraMap F K ((a : F) + c))) :
    algebraMap F K c ≠ 0 ∧ (algebraMap F K c)⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a ∈ SP K 𝔭 := by
  haveI := h𝔭.isPrime
  obtain ⟨hmem, hnot⟩ := mem_pow_vF_of_ne_zero h𝔭 ha
  have hne : 𝔭 ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨π, hu.mem, hu.ne_zero⟩
  obtain ⟨t, ht, z, hz, hzeq⟩ := hac
  have hint : IsIntegral ℤ ((t : F) * ((a : F) + c)) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F K) (algebraMap F K).injective]
    have hzK : IsScalarTower.toAlgHom ℤ F K ((t : F) * ((a : F) + c)) = algebraMap (𝓞 K) K z := by
      rw [IsScalarTower.coe_toAlgHom', hzeq, map_mul]
      rfl
    rw [hzK]
    exact RingOfIntegers.isIntegral_coe z
  obtain ⟨y, hyF⟩ : ∃ y : 𝓞 F, (y : F) = (t : F) * ((a : F) + c) := ⟨⟨_, hint⟩, rfl⟩
  have hyz : algebraMap (𝓞 F) (𝓞 K) y = z := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hzeq]
    show algebraMap F K (y : F) = _
    rw [hyF, map_mul]
    rfl
  have hy2 : y ∈ 𝔭 ^ (2 * vF 𝔭 a) := (idealPowerSpanBounds.mem_pow_iff (K := K) _ _ _).mp (hyz ▸ hz)
  have hy1 : y ∈ 𝔭 ^ (vF 𝔭 a + 1) := Ideal.pow_le_pow_right (by omega) hy2
  obtain ⟨C, hCdef⟩ : ∃ C : 𝓞 F, C = y - t * a := ⟨_, rfl⟩
  have hCF : (C : F) = (t : F) * c := by
    rw [hCdef]
    push_cast
    linear_combination hyF
  have hC1 : C ∈ 𝔭 ^ vF 𝔭 a := by
    rw [hCdef]
    exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (by omega) hy2) (Ideal.mul_mem_left _ _ hmem)
  have hta : t * a ∉ 𝔭 ^ (0 + vF 𝔭 a + 1) :=
    idealPowerSpanBounds.mul_notMem h𝔭.isPrime hne (by rw [zero_add, pow_one]; exact ht) hnot
  have hC2 : C ∉ 𝔭 ^ (vF 𝔭 a + 1) := by
    intro h
    apply hta
    rw [zero_add]
    have hta' : t * a = y - C := by rw [hCdef]; ring
    rw [hta']
    exact Ideal.sub_mem _ hy1 h
  obtain ⟨b, hb, hbC⟩ := exists_unit_mul_pow_eq_pow_mul_of_isUnif0 h𝔭 hu hC1 hC2
  have hC0 : C ≠ 0 := fun h => hC2 (h ▸ Submodule.zero_mem _)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : (C : F) = 0 := by rw [hCF, mul_zero]
    exact hC0 (by exact_mod_cast h0)
  have hcK : algebraMap F K c ≠ 0 := (map_ne_zero _).mpr hc0
  refine ⟨hcK, mem_SP.mpr ⟨b, hb, algebraMap (𝓞 F) (𝓞 K) (t * s₀ ^ vF 𝔭 a), ?_⟩⟩
  show algebraMap F K ((t * s₀ ^ vF 𝔭 a : 𝓞 F) : F) =
    algebraMap F K (b : F) * ((algebraMap F K c)⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a)
  have h2 := congrArg (fun x : 𝓞 F => (x : F)) hbC
  push_cast at h2
  have h3 : (b : F) * (π : F) ^ vF 𝔭 a = (s₀ : F) ^ vF 𝔭 a * ((t : F) * c) := by
    rw [← hCF]
    exact_mod_cast h2
  have hbK : algebraMap F K (b : F) * algebraMap F K (π : F) ^ vF 𝔭 a =
      algebraMap F K (s₀ : F) ^ vF 𝔭 a * (algebraMap F K (t : F) * algebraMap F K c) := by
    have h4 := congrArg (algebraMap F K) h3
    simpa [map_mul, map_pow] using h4
  have hc : ((t * s₀ ^ vF 𝔭 a : 𝓞 F) : F) = (t : F) * (s₀ : F) ^ vF 𝔭 a := by simp
  rw [hc, map_mul, map_pow, ← mul_assoc, mul_comm (algebraMap F K (b : F)), mul_assoc, hbK]
  field_simp

theorem pair_solve {q a c r X Y : K} (hq : q ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hr : a + c = q ^ 2 * r) :
    (X * q * (a⁻¹ * q) - Y * (a⁻¹ * q)) * (q⁻¹ ^ 2 * (a + c)) +
        (Y * r * (a⁻¹ * q) * (c⁻¹ * q) - X * (a⁻¹ * q)) * (q⁻¹ * c) = X ∧
      (X * q * (a⁻¹ * q) - Y * (a⁻¹ * q)) * (q⁻¹ * c) +
        (Y * r * (a⁻¹ * q) * (c⁻¹ * q) - X * (a⁻¹ * q)) * c = Y := by
  obtain rfl : c = q ^ 2 * r - a := by rw [← hr]; ring
  constructor
  · field_simp
    ring
  · field_simp
    ring

theorem pair_coeffs_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {q a c r X Y : K}
    (hp : q ∈ SP K 𝔭) (hua : a⁻¹ * q ∈ SP K 𝔭) (huc : c⁻¹ * q ∈ SP K 𝔭) (hr : r ∈ SP K 𝔭)
    (hX : X ∈ SP K 𝔭) (hY : Y ∈ SP K 𝔭) :
    X * q * (a⁻¹ * q) - Y * (a⁻¹ * q) ∈ SP K 𝔭 ∧
      Y * r * (a⁻¹ * q) * (c⁻¹ * q) - X * (a⁻¹ * q) ∈ SP K 𝔭 := by
  exact ⟨(SP K 𝔭).sub_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem hX hp) hua) ((SP K 𝔭).mul_mem hY hua),
    (SP K 𝔭).sub_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem hY hr) hua) huc)
      ((SP K 𝔭).mul_mem hX hua)⟩

section Vec

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_locF_of_SP {𝔭 : Ideal (𝓞 F)} [hp : 𝔭.IsPrime] {L : Submodule (𝓞 K) V} {r : K}
    (hr : r ∈ SP K 𝔭) {v : V} (hv : v ∈ L) : r • v ∈ locF 𝔭 L := by
  obtain ⟨t, ht, z, hz⟩ := mem_SP.mp hr
  refine ⟨algebraMap (𝓞 F) (𝓞 K) t, Submonoid.subset_closure ⟨t, ht, rfl⟩, ?_⟩
  have he : algebraMap (𝓞 F) (𝓞 K) t • r • v = z • v := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) (r • v), smul_smul, ← hz, algebraMap_smul]
  rw [he]
  exact L.smul_mem z hv

theorem eq_zero_of_orth {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) {ι' : Type}
    (G : ι' → V) (hG : Submodule.span K (Set.range G) = ⊤) {z : V} (hz : ∀ s, h (G s) z = 0) :
    z = 0 := by
  apply hnd
  intro y
  have hy : y ∈ Submodule.span K (Set.range G) := hG ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [← hs.eq, hz s, map_zero]
  | zero => simp
  | add x w _ _ hx hw => rw [map_add, hx, hw, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

end Vec

end Formalism.L2.SG.Pf.UnitPairSolutions
