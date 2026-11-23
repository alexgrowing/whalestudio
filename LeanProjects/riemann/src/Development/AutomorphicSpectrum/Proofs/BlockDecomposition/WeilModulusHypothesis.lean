import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.NormModulus

section One
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem vle_iff_modulus_le (a b : K) : a ≤ᵥ b ↔ modulus a ≤ modulus b := by
  by_cases hb : b = 0
  · subst hb
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
    simp
  have hb' : ValuativeRel.valuation K b ≠ 0 := by simpa using hb
  have h1 : a ≤ᵥ b ↔ a / b ∈ 𝒪[K] := by
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K), Valuation.mem_integer_iff, map_div₀,
      div_le_one₀ (zero_lt_iff.2 hb')]
  rw [h1, ← modulus_le_one_iff, div_eq_mul_inv, modulus_mul, modulus_inv,
    ← div_eq_mul_inv, div_le_one₀ (modulus_pos hb)]

theorem modulus_pow_nat (a : K) (n : ℕ) : modulus (a ^ n) = modulus a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, modulus_mul, ih]

theorem tendsto_pow_zero_of_modulus_lt_one {a : K} (ha : modulus a < 1) :
    Filter.Tendsto (fun n : ℕ => a ^ n) Filter.atTop (nhds 0) := by
  refine (hasBasis_nhds_zero_valBall (K := K)).tendsto_right_iff.2 fun n _ => ?_
  have hlim : Filter.Tendsto (fun k : ℕ => modulus a ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one zero_le ha
  have hq : (0 : ℝ≥0) < (residueCard K : ℝ≥0) ^ (-(n - 1)) :=
    zpow_pos (zero_lt_one.trans one_lt_residueCard_nnreal) _
  filter_upwards [hlim.eventually (gt_mem_nhds hq)] with k hk
  by_cases h0 : a ^ k = 0
  · rw [h0]; exact zero_mem _
  rw [SetLike.mem_coe, mem_valBall_iff_le_ord h0]
  rw [← modulus_pow_nat, modulus_of_ne_zero h0] at hk
  have := (zpow_lt_zpow_iff_right₀ one_lt_residueCard_nnreal).1 hk
  omega

end One

section Two
variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E]

theorem modulus_map_le_one (hc : Continuous (algebraMap F E)) {a : F} (ha : modulus a ≤ 1) :
    modulus (algebraMap F E a) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hcomp : IsCompact (𝒪[F] : Set F) := by
    have h := isCompact_valBall (K := F) 0
    rwa [coe_valBall_zero] at h
  obtain ⟨C, hC⟩ := (hcomp.image (continuous_modulus.comp hc)).bddAbove
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
  have hmem : a ^ n ∈ 𝒪[F] := pow_mem (modulus_le_one_iff.1 ha) n
  have h := hC ⟨a ^ n, hmem, rfl⟩
  simp only [Function.comp_apply, map_pow, modulus_pow_nat] at h
  exact absurd h (not_le.2 hn)

theorem modulus_map_lt_one (hc : Continuous (algebraMap F E)) {a : F} (ha : modulus a < 1) :
    modulus (algebraMap F E a) < 1 := by
  by_contra hge
  push Not at hge
  have h := ((continuous_modulus.comp hc).tendsto 0).comp (tendsto_pow_zero_of_modulus_lt_one ha)
  have h1 : (1 : ℝ≥0) ≤ modulus (algebraMap F E 0) := by
    refine ge_of_tendsto' h fun n => ?_
    simp only [Function.comp_apply, map_pow, modulus_pow_nat]
    exact one_le_pow₀ hge
  simp at h1

theorem valuativeExtension_of_continuous (hc : Continuous (algebraMap F E)) : ValuativeExtension F E := by
  refine ⟨fun a b => ?_⟩
  rw [vle_iff_modulus_le, vle_iff_modulus_le]
  by_cases hb : b = 0
  · subst hb
    simp
  have hb' : algebraMap F E b ≠ 0 := by simpa using hb
  have key : modulus (algebraMap F E (a / b)) ≤ 1 ↔ modulus (a / b) ≤ 1 := by
    refine ⟨fun h => ?_, modulus_map_le_one hc⟩
    by_contra hlt
    push Not at hlt
    have h0 : a / b ≠ 0 := by
      intro h0
      simp [h0] at hlt
    have hinv : modulus (a / b)⁻¹ < 1 := by
      rw [modulus_inv]
      exact inv_lt_one_of_one_lt₀ hlt
    have h2 := modulus_map_lt_one (E := E) hc hinv
    rw [map_inv₀, modulus_inv] at h2
    have h3 : 0 < modulus (algebraMap F E (a / b)) := modulus_pos (by simpa using h0)
    have h4 := (inv_lt_one₀ h3).1 h2
    exact absurd h (not_le.2 h4)
  rw [map_div₀, div_eq_mul_inv, modulus_mul, modulus_inv, ← div_eq_mul_inv,
    div_le_one₀ (modulus_pos hb'), div_eq_mul_inv, modulus_mul, modulus_inv, ← div_eq_mul_inv,
    div_le_one₀ (modulus_pos hb)] at key
  exact key

end Two

theorem wMod : Ad3.K.GL2LocalData.WMod := by
  intro F _ _ _ _ _ _ _ χ _ _ E _ _ _ _ _ _ _ hd hc σ _ η _ x
  haveI : ValuativeExtension F E := valuativeExtension_of_continuous hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hd
  haveI : Fact (Module.finrank F E = 2) := ⟨hd⟩
  haveI : Algebra.IsSeparable F E := inferInstance
  exact_mod_cast (GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) x).symm

end GlobalTheory.CompanionTheory.NormModulus
