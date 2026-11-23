import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.ValPow

variable {L : Type} [Field L] [NumberField L]

theorem count_span_int (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (ha : a ≠ 0) :
    FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L a)) =
      -WithZero.log (w.valuation L (algebraMap (𝓞 L) L a)) := by
  classical
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe L w (by simpa using ha),
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha]
  simp

theorem ordF_eq_count (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    ordF w k = FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L)) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (k : L)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by rw [← hab]; simp)
  have ha' : algebraMap (𝓞 L) L a ≠ 0 := by simpa using ha0
  have hb' : algebraMap (𝓞 L) L b ≠ 0 := by simpa using hb0
  unfold ordF
  rw [← hab, div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul L w (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha')
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hb')),
    FractionalIdeal.count_inv, count_span_int w a ha0, count_span_int w b hb0, map_mul, map_inv₀,
    WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha') (inv_ne_zero ((Valuation.ne_zero_iff _).2 hb')), WithZero.log_inv]
  ring

theorem locK_eq_one {χ : HChar L} {w : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt w) (k : Lˣ)
    (hk : w.valuation L ((k : L) - 1) < 1) : χ.locK w k = 1 := by
  refine h _ ?_ ?_
  · unfold IsUnitAt
    have h1 : Valued.v ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) = w.valuation L (k : L) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
    rw [h1]
    have := (w.valuation L).map_one_add_of_lt hk
    rwa [add_sub_cancel] at this
  · have h1 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
        algebraMap L (w.adicCompletion L) ((k : L) - 1) := by
      rw [map_sub, map_one]
      rfl
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) ((k : L) - 1)) =
        w.valuation L ((k : L) - 1) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2]
    rcases eq_or_ne (w.valuation L ((k : L) - 1)) 0 with h0 | h0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hk
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      push_cast
      omega

theorem inf_mul_val_pow : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∉ S → χ.UnrAt w) → (∀ w ∈ S, χ.TameAt w) → ∀ (v : HeightOneSpectrum (𝓞 L)), v ∉ S → ∀ (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → (∀ w ∈ S, w.valuation L ((k : L) - 1) < 1) → χ.inf k * χ.val v ^ h = 1 := by
  classical
  intro L _ _ χ S hS hT v hv h k hk h1
  rw [← GlobalTheory.HeckeProduct.hchar_productRule L χ S hS k,
    Finset.prod_eq_one (fun w hw => locK_eq_one (hT w hw) k (h1 w hw)), mul_one]
  congr 1
  rw [finprod_eq_single _ v]
  · rw [finprod_eq_if, if_pos hv, ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_self, mul_one,
      zpow_natCast]
  · intro w hw
    rw [ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime L w (Ne.symm hw), mul_zero,
      zpow_zero, finprod_one]

end GlobalTheory.Mem.ValPow

end
