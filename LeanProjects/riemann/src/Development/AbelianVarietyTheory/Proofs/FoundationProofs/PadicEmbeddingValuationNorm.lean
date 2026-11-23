import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.PrimeEmbedding

theorem valuation_eq_exp {L : Type} [Field L] [NumberField L] (𝔓 : HeightOneSpectrum (𝓞 L)) {z : L}
    (hz : z ≠ 0) : 𝔓.valuation L z = WithZero.exp (-vAdd 𝔓 z) := by
  unfold vAdd
  rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hz)]

theorem exists_embedding_norm_eq (L : Type) [Field L] [NumberField L] (𝔓 : HeightOneSpectrum (𝓞 L))
    (ℓ : ℕ) [Fact ℓ.Prime] (h : (ℓ : 𝓞 L) ∈ 𝔓.asIdeal) :
    ∃ i : L →+* ℂ_[ℓ], 0 < vAdd 𝔓 (ℓ : L) ∧ ∀ z : L, z ≠ 0 →
      ‖i z‖ = (ℓ : ℝ) ^ (-((vAdd 𝔓 z : ℝ) / (vAdd 𝔓 (ℓ : L) : ℝ))) := by
  obtain ⟨ι, hι⟩ := GlobalTheory.DatumJets.Place.exists_embedding 𝔓 h
  have hw : ∀ y : 𝓞 L, y ∈ 𝔓.asIdeal ↔ ‖ι (y : L)‖ < 1 := fun y => by rw [hι]; rfl
  have hp : ℓ.Prime := Fact.out
  have hl0 : (ℓ : L) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hlR : (0 : ℝ) < ℓ := Nat.cast_pos.2 hp.pos
  have he : 0 < vAdd 𝔓 (ℓ : L) := by
    have h1 : 𝔓.valuation L (algebraMap (𝓞 L) L (ℓ : 𝓞 L)) < 1 :=
      (𝔓.valuation_lt_one_iff_mem (K := L) _).2 h
    rw [map_natCast, valuation_eq_exp 𝔓 hl0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    omega
  have hunit : ∀ u : L, 𝔓.valuation L u = 1 → ‖ι u‖ = 1 := by
    intro u hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    have h1 := GlobalTheory.MomPlace.norm_le_one_of_valuation L ℓ ι 𝔓 hw u hu.le
    have h2 := GlobalTheory.MomPlace.norm_le_one_of_valuation L ℓ ι 𝔓 hw u⁻¹ (by rw [map_inv₀, hu, inv_one])
    rw [map_inv₀, norm_inv] at h2
    have h3 : 0 < ‖ι u‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hu0)
    exact le_antisymm h1 ((inv_le_one₀ h3).1 h2)
  have hnl : ‖(ℓ : ℂ_[ℓ])‖ = (ℓ : ℝ)⁻¹ := by
    have h1 := PadicComplex.norm_extends' ℓ (ℓ : ℚ_[ℓ])
    rw [Padic.norm_p] at h1
    simpa using h1
  refine ⟨ι, he, fun z hz => ?_⟩
  set e := vAdd 𝔓 (ℓ : L) with hedef
  set a := vAdd 𝔓 z with hadef
  have h1 := hunit (z ^ e / (ℓ : L) ^ a) (by
    rw [map_div₀, map_zpow₀, map_zpow₀, valuation_eq_exp 𝔓 hz, valuation_eq_exp 𝔓 hl0,
      ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_sub, ← WithZero.exp_zero]
    congr 1
    simp only [smul_eq_mul, ← hedef, ← hadef]
    ring)
  rw [map_div₀, map_zpow₀, map_zpow₀, map_natCast, norm_div, norm_zpow, norm_zpow, hnl,
    div_eq_one_iff_eq (zpow_ne_zero _ (inv_ne_zero hlR.ne'))] at h1
  have heR : (e : ℝ) ≠ 0 := Int.cast_ne_zero.2 he.ne'
  calc ‖ι z‖ = (‖ι z‖ ^ e) ^ ((e : ℝ)⁻¹) := by
        rw [← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ heR, Real.rpow_one]
    _ = _ := by
        rw [h1, inv_zpow', ← Real.rpow_intCast, ← Real.rpow_mul hlR.le]
        congr 1
        push_cast
        ring

end GlobalTheory.PrimeEmbedding
