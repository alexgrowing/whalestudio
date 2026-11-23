import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremLevel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open GroundTheory.LocalField (maximalAbelianExtension)
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

omit [Algebra K ℂ] in
include hK in

theorem finite_units : Finite (𝓞 K)ˣ := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, hK] at h1
  have hr : Units.rank K = 0 := by
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  have : IsEmpty (Fin (Units.rank K)) := by rw [hr]; infer_instance
  have htors : ∀ x : (𝓞 K)ˣ, x ∈ Units.torsion K := fun x ↦ by
    obtain ⟨⟨ζ, e⟩, hx, -⟩ := Units.exist_unique_eq_mul_prod K x
    rw [Fintype.prod_empty, mul_one] at hx
    rw [hx]
    exact ζ.2
  exact Finite.of_injective (fun x ↦ (⟨x, htors x⟩ : Units.torsion K)) fun a b h ↦
    congrArg Subtype.val h

omit [Algebra K ℂ] [IsTotallyComplex K] in

theorem exists_nat_mul_mem (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : K) :
    ∃ k : ℕ, 0 < k ∧ (k : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.2 (Units.ne_zero 𝔞))
  have halg : IsAlgebraic ℤ (t / a) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hy0) 2, ?_⟩
  have hint : ((y.natAbs ^ 2 : ℕ) : K) * (t / a) ∈ (algebraMap (𝓞 K) K).range := by
    have h2 : IsIntegral ℤ (y • (y • (t / a))) := hy.smul y
    have e : ((y.natAbs ^ 2 : ℕ) : K) * (t / a) = y • (y • (t / a)) := by
      rw [smul_smul, zsmul_eq_mul]
      have hsq : ((y.natAbs : ℕ) : K) ^ 2 = (y : K) ^ 2 := by
        rw [← Int.cast_natCast, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]
      push_cast
      rw [hsq]
      ring
    rw [e]
    exact ⟨⟨_, h2⟩, rfl⟩
  obtain ⟨b, hb⟩ := hint
  have : ((y.natAbs ^ 2 : ℕ) : K) * t = algebraMap (𝓞 K) K b * a := by
    rw [hb]
    field_simp
  rw [this, ← Algebra.smul_def]
  exact (𝔞 : Submodule (𝓞 K) K).smul_mem b ha

include hK in

theorem main_theorem_complexMultiplication (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ} [E.IsElliptic]
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f) :
    ∃! f' : ℂ →+ (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞)) f' ∧
      ∀ t y : K, IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
        f' (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) := by
  classical
  have := finite_units hK
  have hLs := lattice_idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞)

  have hlev : ∀ n : ℕ, ∃ F : ℂ →+ (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞)) F ∧
      ∀ t y : K, (((n + 1).factorial : ℕ) : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
        IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
          F (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) :=
    fun n ↦ exists_uniformization_level hK σ s hs 𝔞 hf (Nat.factorial_ne_zero (n + 1))
  choose F hF hFp using hlev
  have hF' : ∀ n, IsAnalyticUniformization
      (idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞)).lattice (F n) := fun n ↦ by
    rw [hLs]
    exact hF n

  have hc : ∀ n, ∃ ε : (𝓞 K)ˣ, ∀ z, F n z = F 0 (algebraMap K ℂ (algebraMap (𝓞 K) K ε) * z) := by
    intro n
    obtain ⟨c, -, hcl, hcz⟩ := exists_mul_eq_of_isAnalyticUniformization (hF' 0) (hF' n)
    rw [hLs] at hcl
    obtain ⟨ε, rfl⟩ := exists_unit_of_forall_mem_iff (algebraMap K ℂ) hK _ hcl
    exact ⟨ε, hcz⟩
  choose ε hε using hc

  obtain ⟨ε₀, hinf⟩ := Finite.exists_infinite_fiber ε
  have hinf' : (ε ⁻¹' {ε₀}).Infinite := Set.infinite_coe_iff.1 hinf
  obtain ⟨n₀, hn₀⟩ := hinf'.nonempty
  have hprop : ∀ t y : K,
      IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
        F n₀ (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) := by
    intro t y hq
    obtain ⟨k, hk0, hk⟩ := exists_nat_mul_mem 𝔞 t
    obtain ⟨n, hn, hkn⟩ := hinf'.exists_gt k
    obtain ⟨q, hq'⟩ := Nat.dvd_factorial hk0 (show k ≤ n + 1 by omega)
    have hmt : (((n + 1).factorial : ℕ) : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [hq', Nat.cast_mul, mul_comm (k : K), mul_assoc]
      have h := (𝔞 : Submodule (𝓞 K) K).smul_mem (q : 𝓞 K) hk
      rwa [Algebra.smul_def, map_natCast] at h
    have e₀ : ε n₀ = ε₀ := hn₀
    have e₁ : ε n = ε₀ := hn
    rw [hε n₀, e₀, ← e₁, ← hε n]
    exact hFp n t y hmt hq
  refine ⟨F n₀, ⟨hF n₀, hprop⟩, fun g ⟨hg, hgp⟩ ↦ ?_⟩

  have hg' : IsAnalyticUniformization (idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞)).lattice g := by
    rw [hLs]
    exact hg
  obtain ⟨c, -, -, hcz⟩ := exists_mul_eq_of_isAnalyticUniformization (hF' n₀) hg'
  have hker : ∀ y : K, (c - 1) * algebraMap K ℂ y ∈
      (idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞)).lattice := by
    intro y
    obtain ⟨q, hq⟩ := (IdeleGroup.smulQuotient s⁻¹ 𝔞).surjective (Submodule.Quotient.mk y)
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h1 := hgp t y hq
    have h2 := hprop t y hq
    rw [hcz] at h1
    have h3 : F n₀ ((c - 1) * algebraMap K ℂ y) = 0 := by
      rw [sub_mul, one_mul, map_sub, h1, h2, sub_self]
    exact ((hF' n₀).map_eq_zero_iff _).1 h3
  have hc1 : c = 1 := by
    by_contra hne
    obtain ⟨δ, hδ, hδl⟩ := exists_pos_le_norm (idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞))
    obtain ⟨N, hN⟩ := exists_nat_gt (‖c - 1‖ / δ)
    have hmem := hker ((N + 1 : ℕ) : K)⁻¹
    have hval : algebraMap K ℂ ((N + 1 : ℕ) : K)⁻¹ = ((N + 1 : ℕ) : ℂ)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [hval] at hmem
    have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hne' : (c - 1) * ((N + 1 : ℕ) : ℂ)⁻¹ ≠ 0 :=
      mul_ne_zero (sub_ne_zero.2 hne) (inv_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero N)))
    have hle := hδl _ hmem hne'
    rw [norm_mul, norm_inv, Complex.norm_natCast] at hle
    have h1 : ‖c - 1‖ < δ * (N + 1 : ℕ) := by
      rw [div_lt_iff₀ hδ] at hN
      push_cast
      nlinarith
    have h2 : δ * (N + 1 : ℕ) ≤ ‖c - 1‖ := by
      rw [← le_div_iff₀ hpos, div_eq_mul_inv]
      exact hle
    linarith
  ext z
  rw [hcz, hc1, one_mul]

end

end Elliptic
end GroundTheory.Global
