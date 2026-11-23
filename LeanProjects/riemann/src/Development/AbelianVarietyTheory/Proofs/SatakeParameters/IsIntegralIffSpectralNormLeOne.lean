import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ClosureIso

open Polynomial

section localPart

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 F)}

theorem exists_ne_zero_valued_lt_one (v : HeightOneSpectrum (𝓞 K)) :
    ∃ c : v.adicCompletion K, c ≠ 0 ∧ Valued.v c < 1 := by
  obtain ⟨x, hx⟩ := v.valuation_surjective K (WithZero.exp (-1))
  have hxv : Valued.v (algebraMap K (v.adicCompletion K) x) = WithZero.exp (-1) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans hx
  refine ⟨algebraMap K _ x, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero] at hxv
    exact WithZero.exp_ne_zero hxv.symm
  · rw [hxv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem valued_map_le_one (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f)
    {x : v.adicCompletion K} (hx : Valued.v x ≤ 1) : Valued.v (f x) ≤ 1 := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_valued_lt_one v
  have hN : ∀ N : ℕ, ‖f c‖ * ‖f x‖ ^ N < 1 := by
    intro N
    have h1 : Valued.v (c * x ^ N) < 1 := by
      rw [Valuation.map_mul, Valuation.map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one₀ zero_le hx)) hc1
    have h2 := GlobalTheory.ConjParahoric.val_lt_one_map f hf h1
    rw [← Valued.toNormedField.norm_lt_one_iff] at h2
    simpa [map_mul, map_pow, norm_mul, norm_pow] using h2
  by_contra hgt
  rw [← Valued.toNormedField.norm_le_one_iff, not_le] at hgt
  have hfc : 0 < ‖f c‖ := norm_pos_iff.2 ((map_ne_zero f).2 hc0)
  obtain ⟨N, hN'⟩ := pow_unbounded_of_one_lt (‖f c‖⁻¹) hgt
  have := hN N
  have h3 : 1 < ‖f c‖ * ‖f x‖ ^ N := by
    calc (1 : ℝ) = ‖f c‖ * ‖f c‖⁻¹ := (mul_inv_cancel₀ hfc.ne').symm
      _ < ‖f c‖ * ‖f x‖ ^ N := mul_lt_mul_of_pos_left hN' hfc
  linarith

def intMap (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f) :
    v.adicCompletionIntegers K →+* v'.adicCompletionIntegers F :=
  (f.comp (v.adicCompletionIntegers K).subtype).codRestrict (v'.adicCompletionIntegers F).toSubring
    (fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (valued_map_le_one f hf ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2)))

theorem isIntegral_map (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f)
    (b : Kbar v ≃+* Kbar v') (hb : ∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) {y : Kbar v}
    (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    IsIntegral (v'.adicCompletionIntegers F) (b y) := by
  refine IsIntegral.map_of_comp_eq (intMap f hf) b.toRingHom ?_ hy
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v),
    IsScalarTower.algebraMap_apply (v'.adicCompletionIntegers F) (v'.adicCompletion F) (Kbar v'), hb]
  rfl

theorem valued_le_one_of_isIntegral {x : v'.adicCompletion F}
    (hx : IsIntegral (v'.adicCompletionIntegers F) (algebraMap (v'.adicCompletion F) (Kbar v') x)) :
    Valued.v x ≤ 1 := by
  rw [isIntegral_algebraMap_iff (algebraMap (v'.adicCompletion F) (Kbar v')).injective] at hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2

end localPart

section spectral

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 F)}

theorem isIntegral_iff_spectralNorm_le_one (y : Kbar v) :
    IsIntegral (v.adicCompletionIntegers K) y ↔ spectralNorm (v.adicCompletion K) (Kbar v) y ≤ 1 := by
  have hyK : IsIntegral (v.adicCompletion K) y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyK)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (v.adicCompletion K) hy, coeff_map]
    exact Valued.toNormedField.norm_le_one_iff.2
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((minpoly (v.adicCompletionIntegers K) y).coeff n).2)
  · intro h
    have hl : minpoly (v.adicCompletion K) y ∈
        lifts (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        (Valued.toNormedField.norm_le_one_iff.1 (h n))⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyK)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap (v.adicCompletion K), hq, minpoly.aeval]

theorem exists_isIntegral_mul_inv_pow {y : Kbar v} (hy : ¬ IsIntegral (v.adicCompletionIntegers K) y)
    {c : v.adicCompletion K} (hc : c ≠ 0) :
    ∃ N : ℕ, IsIntegral (v.adicCompletionIntegers K) (algebraMap _ (Kbar v) c⁻¹ * y⁻¹ ^ N) := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_ne_zero_valued_lt_one v
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    NontriviallyNormedField.ofNormNeOne ⟨ϖ, hϖ0, (Valued.toNormedField.norm_lt_one_iff.2 hϖ1).ne⟩
  have hmul : ∀ a b : Kbar v, spectralNorm (v.adicCompletion K) (Kbar v) (a * b) =
      spectralNorm (v.adicCompletion K) (Kbar v) a * spectralNorm (v.adicCompletion K) (Kbar v) b :=
    fun a b => spectralAlgNorm_mul a b
  have hy1 : 1 < spectralNorm (v.adicCompletion K) (Kbar v) y := by
    rw [isIntegral_iff_spectralNorm_le_one, not_le] at hy
    exact hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy isIntegral_zero
  have hinv : spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ *
      spectralNorm (v.adicCompletion K) (Kbar v) y = 1 := by
    rw [← hmul, inv_mul_cancel₀ hy0, spectralNorm_one]
  have hlt : spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ < 1 := by
    rw [eq_inv_of_mul_eq_one_left hinv]
    exact inv_lt_one_of_one_lt₀ hy1
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc' hlt
  refine ⟨n + 1, ?_⟩
  have hs0 : 0 ≤ spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ := spectralNorm_nonneg _
  rw [isIntegral_iff_spectralNorm_le_one, hmul, spectralNorm_extends,
    isPowMul_spectralNorm _ (by omega : 1 ≤ n + 1)]
  calc ‖c⁻¹‖ * spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ ^ (n + 1)
      ≤ ‖c⁻¹‖ * spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs0 hlt.le (by omega)) (norm_nonneg _)
    _ ≤ ‖c⁻¹‖ * ‖c‖ := mul_le_mul_of_nonneg_left hn.le (norm_nonneg _)
    _ = 1 := by rw [norm_inv, inv_mul_cancel₀ hc'.ne']

theorem isIntegral_map_iff (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f)
    (b : Kbar v ≃+* Kbar v') (hb : ∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) (y : Kbar v) :
    IsIntegral (v'.adicCompletionIntegers F) (b y) ↔ IsIntegral (v.adicCompletionIntegers K) y := by
  refine ⟨fun h => ?_, isIntegral_map f hf b hb⟩
  by_contra hy
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_valued_lt_one v
  obtain ⟨N, hN⟩ := exists_isIntegral_mul_inv_pow hy hc0
  have h1 := isIntegral_map f hf b hb hN
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy isIntegral_zero
  have hby0 : b y ≠ 0 := (map_ne_zero b).2 hy0
  have h2 : IsIntegral (v'.adicCompletionIntegers F)
      (algebraMap (v'.adicCompletion F) (Kbar v') (f c)⁻¹) := by
    have e : algebraMap (v'.adicCompletion F) (Kbar v') (f c)⁻¹ =
        b y ^ N * b (algebraMap (v.adicCompletion K) (Kbar v) c⁻¹ * y⁻¹ ^ N) := by
      rw [map_mul, map_pow, map_inv₀ b y, hb, map_inv₀ f, inv_pow, mul_left_comm,
        mul_inv_cancel₀ (pow_ne_zero _ hby0), mul_one]
    rw [e]
    exact (h.pow N).mul h1
  have h3 := valued_le_one_of_isIntegral h2
  have h4 := GlobalTheory.ConjParahoric.val_lt_one_map f hf hc1
  have hfc : f c ≠ 0 := (map_ne_zero f).2 hc0
  have h5 : Valued.v (f c * (f c)⁻¹) < 1 := by
    rw [Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h3) h4
  rw [mul_inv_cancel₀ hfc, Valuation.map_one] at h5
  exact lt_irrefl _ h5

end spectral

end GlobalTheory.ClosureIso
