import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.CompHt

theorem norm_algebraMap_lt_one_iff_valuation_lt_one : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra K ℂ_[ℓ]], (ℓ : 𝓞 K) ∈ la.asIdeal → ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ (k : T.Fr →+* ℂ_[ℓ]), (∀ b, k (io b) = algebraMap K ℂ_[ℓ] b) →
      (∀ x : T.Fr, val_vw la ℓ (Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (k x) = nval T.V e x) →
      ∀ b : K, ‖algebraMap K ℂ_[ℓ] b‖ < 1 ↔ la.valuation K b < 1 := by
  intro K _ _ la ℓ _ _ hℓ T io e ho k hk hm b
  have hnv : ∀ x : ℂ_[ℓ], ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := fun x => by
    rw [PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  by_cases hb : b = 0
  · subst hb; simp

  have hpos : ∀ x : K, x ≠ 0 → (0 < vLa la x ↔ la.valuation K x < 1) := fun x hx => by
    have h0 : la.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have := WithZero.log_lt_log h0 (one_ne_zero)
    rw [WithZero.log_one] at this
    simp only [vLa]
    constructor
    · intro h; exact this.1 (by omega)
    · intro h; have := this.2 h; omega
  have hℓK : (ℓ : K) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hcpos : (0 : ℝ) < vLa la (ℓ : K) := by
    have h1 : la.valuation K (ℓ : K) < 1 := by
      have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) la (ℓ : 𝓞 K)).2 hℓ
      simpa using this
    exact_mod_cast (hpos _ hℓK).2 h1
  have ha : algebraMap K ℂ_[ℓ] b ≠ 0 := (map_ne_zero _).2 hb
  have hio : io b ≠ 0 := (map_ne_zero _).2 hb
  have h := hm (io b)
  rw [hk, val_vw_of_ne la ℓ _ ha, nval_of_ne hio, ho.2 b] at h
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h' : (vLa la (ℓ : K) : ℝ) * (Real.log ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (algebraMap K ℂ_[ℓ] b) : ℝ) /
      Real.log ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (ℓ : ℂ_[ℓ]) : ℝ)) = vLa la b := by
    rw [EReal.coe_eq_coe_iff] at h
    rw [h]; push_cast; field_simp
  have hL : Real.log ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (ℓ : ℂ_[ℓ]) : ℝ) < 0 := by
    rw [PadicComplex.valuation_p]
    have : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    push_cast
    exact Real.log_neg (by positivity) (by rw [one_div]; exact inv_lt_one_of_one_lt₀ this)
  have hva : (0 : ℝ) < ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (algebraMap K ℂ_[ℓ] b) : ℝ) := by
    have : (Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (algebraMap K ℂ_[ℓ] b) ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    exact_mod_cast pos_iff_ne_zero.2 this
  rw [hnv, ← hpos b hb, ← Int.cast_pos (R := ℝ), ← h', mul_pos_iff_of_pos_left hcpos,
    ← Real.log_neg_iff hva]
  constructor
  · intro hA; exact div_pos_of_neg_of_neg hA hL
  · intro hq
    by_contra hA; push_neg at hA
    exact absurd hq (not_lt.2 (div_nonpos_of_nonneg_of_nonpos hA hL.le))

end GlobalTheory.CompHt
