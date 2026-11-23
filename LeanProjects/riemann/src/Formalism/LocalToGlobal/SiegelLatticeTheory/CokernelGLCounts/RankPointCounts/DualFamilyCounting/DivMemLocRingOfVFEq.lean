import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsHermSemilocalLocRing
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOfNormRepCountNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountExtP
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeVdLeOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem κι_eq (t : 𝓞 F) : κ (ι t) = algebraMap F K (t : F) := rfl

theorem κι_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : κ (ι a) ≠ 0 := by
  intro h
  apply ha
  have h1 : ι a = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])
  exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (by rw [h1, map_zero])

theorem exists_mul_eq_of_vF_eq {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a a' : 𝓞 F}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hv : vF 𝔭 a = vF 𝔭 a') :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c : 𝓞 F, t * a' = c * a := by
  have h1 : Ideal.span {a} ≤ 𝔭 ^ vF 𝔭 a :=
    (Ideal.span_singleton_le_iff_mem _).2 (localValuationFiltration.mem_pow_vF h𝔭 ha)
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 h1
  have hQp : ¬ Q ≤ 𝔭 := by
    intro hle
    apply localValuationFiltration.notMem_pow_vF h𝔭 ha
    have : Ideal.span {a} ≤ 𝔭 ^ (vF 𝔭 a + 1) := by
      rw [hQ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact this (Ideal.subset_span rfl)
  obtain ⟨t, htQ, htp⟩ := Set.not_subset.1 hQp
  refine ⟨t, htp, ?_⟩
  have ha'v : a' ∈ 𝔭 ^ vF 𝔭 a := by
    rw [hv]
    exact localValuationFiltration.mem_pow_vF h𝔭 ha'
  have h2 : a' * t ∈ Ideal.span {a} := by
    rw [hQ]
    exact Ideal.mul_mem_mul ha'v htQ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h2
  exact ⟨c, by rw [mul_comm, hc]⟩

variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
include hK hF

theorem mem_locRing_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (z : K) :
    z ∈ WA.locRing P ↔ ∃ t : 𝓞 F, t ∉ P.comap ι ∧ ∃ r : 𝓞 K, κ r = κ (ι t) * z := by
  have hp : (P.comap ι).IsPrime := Ideal.comap_isPrime _ _
  rw [WA.mem_locRing, UnimodularLocalization.locR_eq_locF hK hF hP, LocF.mem_locF_iff hp]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [Submodule.mem_one, Algebra.smul_def]

theorem div_mem_locRing_of_vF_eq {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {a a' : 𝓞 F}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hv : vF (P.comap ι) a = vF (P.comap ι) a') :
    κ (ι a') / κ (ι a) ∈ WA.locRing P := by
  have hpm : (P.comap ι).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  obtain ⟨t, ht, c, hc⟩ := exists_mul_eq_of_vF_eq hpm ha ha' hv
  rw [mem_locRing_iff hK hF hP]
  refine ⟨t, ht, ι c, ?_⟩
  have h0 := κι_ne_zero (K := K) ha
  have e : κ (ι t) * κ (ι a') = κ (ι c) * κ (ι a) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hc]
  field_simp
  rw [e]

theorem exists_norm_one_unit {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {μ : K} (hμ : μ ≠ 0)
    (hN : star μ * μ ∈ WA.locRing P) (hN' : (star μ * μ)⁻¹ ∈ WA.locRing P) :
    ∃ b : K, star b * b = 1 ∧ b * μ⁻¹ ∈ WA.locRing P ∧ μ * b⁻¹ ∈ WA.locRing P := by
  have hS := WA.isHermSemilocal_locRing hK hP
  have h1 : star μ⁻¹ * μ⁻¹ ∈ WA.locRing P := by
    rw [star_inv₀, ← mul_inv]
    exact hN'
  obtain ⟨b, hb, hbm⟩ := WA.exists_norm_one_mul_mem hS h1
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have hsb : star b = b⁻¹ := eq_inv_of_mul_eq_one_left hb
  refine ⟨b, hb, by rw [mul_comm]; exact hbm, ?_⟩
  have e : μ * b⁻¹ = star (μ⁻¹ * b) * (star μ * μ) := by
    rw [star_mul', star_inv₀, hsb]
    have hsμ : star μ ≠ 0 := star_ne_zero.2 hμ
    field_simp
  rw [e]
  exact (WA.locRing P).mul_mem (hS.star_mem _ hbm) hN

section Line

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_locF_span_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (x z : V) :
    z ∈ locF (P.comap ι) (Submodule.span (𝓞 K) {x}) ↔ ∃ c ∈ WA.locRing P, z = c • x := by
  have hp : (P.comap ι).IsPrime := Ideal.comap_isPrime _ _
  rw [LocF.mem_locF_iff hp]
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hz
    have ht0 : κ (ι t) ≠ 0 := κι_ne_zero (fun h => ht (h ▸ Ideal.zero_mem _))
    refine ⟨κ r / κ (ι t), (mem_locRing_iff hK hF hP _).2 ⟨t, ht, r, by field_simp⟩, ?_⟩
    have e1 : r • x = κ r • x := (algebraMap_smul K r x).symm
    have e2 : ι t • z = κ (ι t) • z := (algebraMap_smul K (ι t) z).symm
    rw [e1, e2] at hr
    rw [div_eq_inv_mul, mul_smul, hr, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨t, ht, r, hr⟩ := (mem_locRing_iff hK hF hP c).1 hc
    refine ⟨t, ht, Submodule.mem_span_singleton.2 ⟨r, ?_⟩⟩
    rw [← algebraMap_smul K r x, ← algebraMap_smul K (ι t) (c • x), smul_smul, hr]

omit hK hF in
theorem h_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (μ ν : K) (x y : V) :
    h (μ • x) (ν • y) = star μ * ν * h x y := by
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  ring

theorem exists_isom_line {h : V →ₗ⋆[K] V →ₗ[K] K} (hV : finrank K V = 1) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x x' : V} {a a' : 𝓞 F}
    (hx : h x x = algebraMap F K (a : F)) (hx' : h x' x' = algebraMap F K (a' : F))
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hv : vF 𝔭 a = vF 𝔭 a') :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 (Submodule.span (𝓞 K) {x})) =
      locF 𝔭 (Submodule.span (𝓞 K) {x'}) := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  rw [← κι_eq] at hx hx'
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [map_zero, LinearMap.zero_apply] at hx
    exact κι_ne_zero ha hx.symm
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' x hx0).1 hV x'
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    rw [← hμ] at hx'
    simp only [map_zero, LinearMap.zero_apply] at hx'
    exact κι_ne_zero ha' hx'.symm
  have hN : star μ * μ = κ (ι a') / κ (ι a) := by
    have e := h_smul_smul h μ μ x x
    rw [hμ, hx, hx'] at e
    rw [e]
    field_simp [κι_ne_zero (K := K) ha]
  have hS1 : star μ * μ ∈ WA.locRing P := by
    rw [hN]
    exact div_mem_locRing_of_vF_eq hK hF hP ha ha' hv
  have hS2 : (star μ * μ)⁻¹ ∈ WA.locRing P := by
    rw [hN, inv_div]
    exact div_mem_locRing_of_vF_eq hK hF hP ha' ha hv.symm
  obtain ⟨b, hb, hb1, hb2⟩ := exists_norm_one_unit hK hF hP hμ0 hS1 hS2
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  refine ⟨LinearEquiv.smulOfNeZero K V b hb0, ?_, ?_⟩
  · intro y z
    change h (b • y) (b • z) = h y z
    rw [h_smul_smul, hb, one_mul]
  · ext z
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      LinearEquiv.smulOfNeZero_apply]
    rw [mem_locF_span_iff hK hF hP x' z]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_locF_span_iff hK hF hP x y).1 hy
      refine ⟨b * μ⁻¹ * c, (WA.locRing P).mul_mem hb1 hc, ?_⟩
      rw [← hμ, smul_smul, smul_smul]
      congr 1
      field_simp
    · rintro ⟨c, hc, rfl⟩
      refine ⟨(c * (μ * b⁻¹)) • x,
        (mem_locF_span_iff hK hF hP x _).2 ⟨_, (WA.locRing P).mul_mem hc hb2, rfl⟩, ?_⟩
      rw [← hμ, smul_smul, smul_smul]
      congr 1
      field_simp

theorem jordanIsom_rank_one [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hV : finrank K V = 1)
    {L L' : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {b b' : Fin (finrank K (⊤ : Submodule K V)) → V} {a a' : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F}
    (hJ : Cnt.IsJordanIn h ⊤ L 𝔭 b a) (hJ' : Cnt.IsJordanIn h ⊤ L' 𝔭 b' a')
    (hv : ∀ i, vF 𝔭 (a i) = vF 𝔭 (a' i)) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L' := by
  have hn : finrank K (⊤ : Submodule K V) = 1 := by rw [finrank_top]; exact hV
  let i0 : Fin (finrank K (⊤ : Submodule K V)) := ⟨0, by omega⟩
  have hr : ∀ c : Fin (finrank K (⊤ : Submodule K V)) → V, Set.range c = {c i0} := by
    intro c
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      have hj := j.isLt
      congr 1
      exact Fin.ext (by simp only [i0]; omega)
    · rintro rfl
      exact ⟨i0, rfl⟩
  obtain ⟨-, hL, -, hbb, ha0⟩ := hJ
  obtain ⟨-, hL', -, hbb', ha0'⟩ := hJ'
  rw [← hL, ← hL', hr b, hr b']
  exact exists_isom_line hK hF hV h𝔭 (hbb i0) (hbb' i0) (ha0 i0) (ha0' i0) (hv i0)

end Line

theorem exists_norm_congr_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ∉ 𝔭) {k : ℕ}
    (hk : 1 ≤ k) : ∃ α : 𝓞 K, conjO K α * α - ι c ∈ extP K 𝔭 ^ k := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hcP : ι c ∉ P := fun h => hc (Ideal.mem_comap.2 h)
  have hN := IdealNormInequalities.one_lt_absNorm hP
  obtain ⟨h1, h2⟩ := localDensity K hK P hP 1 k le_rfl hk (ι c) (idealPowerSpanBounds.conjO_map hF c) hcP
  by_cases hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have h3 := h1 hc'
    have hs : 0 < Real.sqrt (Ideal.absNorm P : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hpos : (0 : ℝ) < (normRepCount K (P ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos hs _) ?_
      have : (0 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) := zpow_pos hs _
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hc']
    exact hα
  · have h3 := h2 hc'
    have hpos : (0 : ℝ) < (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos (by linarith) _) ?_
      have : (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
        rw [Nat.cast_one, zpow_neg_one]
        exact inv_lt_one_of_one_lt₀ hN
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.extP_split hK hF hP hc']
    exact hα

end Formalism.L2.SG.Pf.TemperedBoundGL3
