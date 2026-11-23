import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SubstCongrModPrimeOfIntegralDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowPrimePowSubFrobeniusTwistNormLeStatement
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

open Formalism.L2.Th1.C

theorem twistLog_norm_iterate {K : Type} [NormedField K] (σ : K →+* K) (hσ : ∀ x : K, ‖σ x‖ = ‖x‖) (i : ℕ)
    (x : K) : ‖(σ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (ih (σ x)).trans (hσ x)

theorem twistLog_additive_mod : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ (i : ℕ), 0 < i → ∀ m,
      ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e (frobOp σ l i f) (MvPowerSeries.X (0 : Fin 2))
        (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l σ hU f e hf i hi m
  have hU' := hU
  obtain ⟨hlp, -, hl1, -, hσn, -⟩ := hU
  obtain ⟨hlog, hd, hint⟩ := hf
  have hlog0 := hlog
  obtain ⟨h0, h1, h0', hfe, hef⟩ := hlog
  have hn : l ^ i ≠ 0 := pow_ne_zero _ hlp.ne_zero
  have hτ : ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := twistLog_norm_iterate σ hσn i
  set g := PowerSeries.map (σ ^ i) f with hg
  set e' := PowerSeries.map (σ ^ i) e with he'
  have hXm : MvPowerSeries.map (σ ^ i) (PowerSeries.X : K⟦X⟧) = PowerSeries.X := PowerSeries.map_X _
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have he0 : PowerSeries.constantCoeff e' = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he', PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0', map_zero]
  have hlog' : IsLogPair g e' := by
    refine ⟨hg0, ?_, he0, ?_, ?_⟩
    · rw [hg, PowerSeries.coeff_map, h1, map_one]
    · have := congrArg (MvPowerSeries.map (σ ^ i)) hfe
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0), hXm] at this
      exact this
    · have := congrArg (MvPowerSeries.map (σ ^ i)) hef
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0'), hXm] at this
      exact this
  have hd' : CoefLe 1 (d⁄dX K g) := by
    intro k
    rw [PowerSeries.coeff_derivative, hg, PowerSeries.coeff_map]
    have hk : (σ ^ i) ((PowerSeries.coeff (k + 1)) f) * ((k : K) + 1)
        = (σ ^ i) ((PowerSeries.coeff (k + 1)) f * ((k : K) + 1)) := by
      rw [map_mul, map_add, map_one, map_natCast]
    rw [hk, hτ, ← PowerSeries.coeff_derivative]
    exact hd k
  set X0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hX0
  set X1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hX1
  have hX00 : MvPowerSeries.constantCoeff X0 = 0 := by simp [X0]
  have hX10 : MvPowerSeries.constantCoeff X1 = 0 := by simp [X1]
  set F := fadd f e X0 X1 with hF
  have hF0 : MvPowerSeries.constantCoeff F = 0 := Pts.constantCoeff_fadd hlog0 hX00 hX10
  have hFint : ∀ m, ‖MvPowerSeries.coeff m F‖ ≤ 1 := fun m => hint m
  have hAB := GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le K l σ hU' (Fin 2) F hFint i hn
  set A := F ^ l ^ i with hA
  set B := MvPowerSeries.expand (l ^ i) hn (MvPowerSeries.map (σ ^ i) F) with hB
  have hA0 : MvPowerSeries.constantCoeff A = 0 := by
    rw [hA, map_pow, hF0, zero_pow hn]
  have hB0 : MvPowerSeries.constantCoeff B = 0 := by
    simp [hB, hF0]
  have hA1 : ∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1 := fun m => IntegralMvPolynomialLemmas.intMv_pow hint (l ^ i) m
  have hB1 : ∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1 := by
    intro m
    have hb : MvPowerSeries.coeff m B
        = MvPowerSeries.coeff m A + -(MvPowerSeries.coeff m (A - B)) := by
      rw [map_sub]
      ring
    rw [hb]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
    exact max_le (hA1 m) ((hAB m).trans hl1.le)
  have key := GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative K l hlp hl1 g hd' (Fin 2) A B hA0 hB0 hA1 hB1 hAB m
  have hsX : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (frobOp σ l i f) = PowerSeries.subst (a ^ l ^ i) g := by
    intro a ha
    have has := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold frobOp
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hn) has,
      PowerSeries.subst_pow has, PowerSeries.subst_X has]
  have hs0 : MvPowerSeries.constantCoeff (PowerSeries.subst X0 g + PowerSeries.subst X1 g) = 0 := by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero hX00 _ hg0,
      PowerSeries.constantCoeff_subst_eq_zero hX10 _ hg0, add_zero]
  have hs0f : MvPowerSeries.constantCoeff (PowerSeries.subst X0 f + PowerSeries.subst X1 f) = 0 := by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero hX00 _ h0,
      PowerSeries.constantCoeff_subst_eq_zero hX10 _ h0, add_zero]
  have hmapF : MvPowerSeries.map (σ ^ i) F
      = PowerSeries.subst (PowerSeries.subst X0 g + PowerSeries.subst X1 g) e' := by
    rw [hF]
    unfold fadd
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs0f), map_add,
      PowerSeries.map_subst (PowerSeries.HasSubst.X 0), PowerSeries.map_subst (PowerSeries.HasSubst.X 1),
      hX0, hX1, MvPowerSeries.map_X, MvPowerSeries.map_X]
  have hBf : B = fadd g e' (X0 ^ l ^ i) (X1 ^ l ^ i) := by
    rw [hB, hmapF, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.of_constantCoeff_zero hs0),
      map_add, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.X 0),
      PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.X 1), hX0, hX1,
      MvPowerSeries.expand_X, MvPowerSeries.expand_X]
    rfl
  have hBeq : PowerSeries.subst B g
      = PowerSeries.subst (X0 ^ l ^ i) g + PowerSeries.subst (X1 ^ l ^ i) g := by
    rw [hBf]
    exact Pts.l_fadd hlog' (by rw [map_pow, hX00, zero_pow hn]) (by rw [map_pow, hX10, zero_pow hn])
  have hbe : be0 f e (frobOp σ l i f) X0 X1 = PowerSeries.subst A g - PowerSeries.subst B g := by
    unfold be0
    rw [← hF, hsX F hF0, hsX X0 hX00, hsX X1 hX10, hBeq]
    abel
  rw [hbe]
  exact key

end GlobalTheory.Honda
