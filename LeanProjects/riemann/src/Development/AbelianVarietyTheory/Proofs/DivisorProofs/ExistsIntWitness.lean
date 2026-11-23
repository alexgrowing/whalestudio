import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKCongr

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.GaussModulus
open Formalism.L2.Host (atFin IsUnitAt)

namespace GlobalTheory.GaussModulus

theorem exists_int_witness {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (ha : a ≠ 0) (hE : ExpAt χ w a) :
    ∃ (y : 𝓞 E) (u : Eˣ), (u : E) = y ∧ y ∉ w.asIdeal ∧ y - 1 ∈ w.asIdeal ^ (a - 1) ∧ χ.locK w u ≠ 1 := by
  have hnot : ¬ χ.LevelLe w (a - 1) := fun h => by
    have := (hE (a - 1)).mp h
    omega
  have hlev : χ.LevelLe w a := (hE a).mpr le_rfl
  simp only [Formalism.L2.Host.HChar.LevelLe, not_forall] at hnot
  obtain ⟨x, hxu, hx1, hxχ⟩ := hnot
  have hxv : Valued.v (x : w.adicCompletion E) = 1 := hxu
  obtain ⟨y, hy⟩ := exists_int_approx w hxv.le a
  have hlt : WithZero.exp (-(a : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hyv' : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = 1 := by
    rw [← hxv]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [Valuation.map_sub_swap, hxv]
    exact lt_of_le_of_lt hy hlt
  have hyv : w.valuation E (y : E) = 1 := by rwa [← valued_algebraMap]
  have hy0 : (y : E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hyv
    exact zero_ne_one hyv
  refine ⟨y, Units.mk0 (y : E) hy0, rfl, ?_, ?_, ?_⟩
  · rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E)]
    exact hyv
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← valued_algebraMap]
    have e : algebraMap E (w.adicCompletion E) ((algebraMap (𝓞 E) E) (y - 1)) =
        (algebraMap E (w.adicCompletion E) (y : E) - (x : w.adicCompletion E)) + ((x : w.adicCompletion E) - 1) := by
      simp
    rw [e]
    refine Valuation.map_add_le _ ?_ hx1
    rw [Valuation.map_sub_swap]
    refine hy.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  · intro hχ
    apply hxχ
    set u : Eˣ := Units.mk0 (y : E) hy0 with hu
    have hau : ((atFin w u : (w.adicCompletion E)ˣ) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (y : E) := rfl
    have h1 : χ.loc w (x * (atFin w u)⁻¹) = 1 := by
      refine hlev _ ?_ ?_
      · show Valued.v (((x * (atFin w u)⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = 1
        rw [Units.val_mul, Units.val_inv_eq_inv_val, hau, map_mul, map_inv₀, hxv, hyv', inv_one, one_mul]
      · rw [Units.val_mul, Units.val_inv_eq_inv_val, hau]
        have hne : algebraMap E (w.adicCompletion E) (y : E) ≠ 0 := by
          intro h; rw [h, map_zero] at hyv'; exact zero_ne_one hyv'
        rw [show (x : w.adicCompletion E) * (algebraMap E (w.adicCompletion E) (y : E))⁻¹ - 1 =
            ((x : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) *
              (algebraMap E (w.adicCompletion E) (y : E))⁻¹ by field_simp]
        rw [map_mul, map_inv₀, hyv', inv_one, mul_one]
        exact hy
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [h1]
    exact hχ

end GlobalTheory.GaussModulus

end
