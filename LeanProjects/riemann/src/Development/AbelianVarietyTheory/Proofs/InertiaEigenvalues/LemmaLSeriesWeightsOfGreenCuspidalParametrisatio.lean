import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightNonnegOfIdempotentGlnPrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightSquarefreeLabelGelfandGStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLowerComparisonStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLeSquarefreeStatement

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem five_le_typePrime (D : Formalism.BasicNotions.D7) (k : Fin 2) : 5 ≤ D.host.g k := by
  have hc := D.ntypes.g_cond k
  have h4 : D.host.g k % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        (((pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd).mul_right _).mul_right _), hc]
  have := (D.host.g_prime k).two_le
  omega

theorem rank_eq_k_add_two_mul (R : Formalism.BasicNotions.Ranks) : R.r = R.k + 2 * (R.m / 2 - 1) + 1 := by
  obtain ⟨a, ha⟩ := R.m_even
  have := R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r
  omega

theorem lemmaL_series_weights_of_greenCuspidalParametrisation : Green → ∀ D : Formalism.BasicNotions.D7, ESerTie D → admLq D := by
  intro hG D hT k ψ hψ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, -, hL⟩ := hT k
  have hw : ∀ a f, wtOf D k a f = wtC L a f := by
    intro a f
    unfold wtOf wtC
    rw [hL f]
  have h5 := five_le_typePrime D k
  have hr := rank_eq_k_add_two_mul D.R
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨hU, hU1, hJ, -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ
  obtain ⟨hJ, hJ1⟩ := hJ hr
  simp only [hw]
  refine ⟨fun f => ⟨?_, ?_⟩, fun f hf hs => ?_, fun f _ => ?_, fun f hf hs => ?_⟩
  · refine GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hU ?_ f
    change 0 ≤ ((eU (D.host.g k) D.R.r ψ).coeff 1).re
    rw [hU1, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  · refine GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hJ ?_ f
    change 0 ≤ ((eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ).coeff 1).re
    rw [hJ1, ← Nat.cast_pow, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  · exact GlobalTheory.T.harishChandraSeriesWeight_squarefree_label_gelfandGraev _ L h5 hG ψ hψ _ f hf.1 hf.2.1 hf.2.2 hs
  · exact GlobalTheory.T.harishChandraSeriesWeight_lower_comparison _ L ψ hψ _ _ _ hr hk f
  · exact GlobalTheory.T.harishChandraSeriesWeight_le_squarefree _ L h5 hG ψ hψ _ _ _ hr hk f hf.1 hf.2.1 hf.2.2 hs

end GlobalTheory.GLq
