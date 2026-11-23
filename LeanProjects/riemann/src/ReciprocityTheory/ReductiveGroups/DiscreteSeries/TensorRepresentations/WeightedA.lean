import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamLeOfKTypes
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ClassTwoEntries
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryB

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

def wdCoef (ε : Fin n → Bool) (w : L2 ε) : smD ε (rreg ε) →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  toFun x := fun g => inner ℂ w (rreg ε g (x : L2 ε))
  map_add' x y := funext fun g => by simp [inner_add_right]
  map_smul' c x := funext fun g => by simp [inner_smul_right]

theorem wdCoef_apply (w : L2 ε) (x : smD ε (rreg ε)) (g : Matrix (Fin n) (Fin n) ℂ) :
    wdCoef ε w x g = inner ℂ w (rreg ε g (x : L2 ε)) := rfl

theorem wdCoef_smooth (w : L2 ε) (x : smD ε (rreg ε)) : Formalism.REAL.SmoothOnG ε (wdCoef ε w x) :=
  smoothOnGV_clm (innerSL ℂ w) ((mem_smD_iff ε (rreg ε) _).1 x.2)

theorem wdCoef_eab (w : L2 ε) (x : smD ε (rreg ε)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : Formalism.REAL.Eab ε a b (wdCoef ε w x) g = wdCoef ε w (smE ε (rreg ε) a b x) g := by
  have hv : IsSmoothVecU ε (rreg ε) (x : L2 ε) := (mem_smD_iff ε (rreg ε) _).1 x.2
  rw [icx_eab_eq, wdCoef_apply, smE_apply (rreg_isURepOn ε), orbit_ecV (rreg_isURepOn ε) _ hv hg]
  exact icx_eabV_clm (innerSL ℂ w) hv a b hg

def wdWord (ε : Fin n → Bool) : List (Fin n × Fin n) → Module.End ℂ (smD ε (rreg ε))
  | [] => 1
  | p :: l => smE ε (rreg ε) p.1 p.2 * wdWord ε l

theorem wdWord_append (x : smD ε (rreg ε)) (a b : Fin n) :
    ∀ l : List (Fin n × Fin n), wdWord ε l (smE ε (rreg ε) a b x) = wdWord ε (l ++ [(a, b)]) x
  | [] => by simp [wdWord]
  | p :: l => by
      simp only [List.cons_append, wdWord, Module.End.mul_apply]
      rw [wdWord_append x a b l]

theorem wdCoef_eword (w : L2 ε) (x : smD ε (rreg ε)) :
    ∀ (l : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.REAL.Eword ε l (wdCoef ε w x) g = wdCoef ε w (wdWord ε l x) g
  | [], g, _ => rfl
  | p :: l, g, hg => by
      simp only [Formalism.REAL.Eword, wdWord, Module.End.mul_apply]
      rw [icx_eab_eq, icx_eabV_congr (fun g' hg' => wdCoef_eword w x l g' hg') p.1 p.2 hg, ← icx_eab_eq]
      exact wdCoef_eab w _ p.1 p.2 hg

theorem wdCoef_cont (w : L2 ε) (x : L2 ε) :
    Continuous (fun g : Formalism.REAL.UJ ε => inner ℂ w (rreg ε (Formalism.MainNotions.S.umat g) x)) := by
  have h : Continuous (fun g : Formalism.REAL.UJ ε => rreg ε (Formalism.MainNotions.S.umat g) x) :=
    ((rreg_isURepOn ε).2.2 x).comp_continuous (continuous_umatA ε) (fun g => g.2)
  exact continuous_const.inner h

theorem wd_hs_cont : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => S7.hs g) := by
  unfold S7.hs
  fun_prop

def wdF (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Formalism.REAL.UJ ε → ℂ :=
  fun g => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * f (Formalism.MainNotions.S.umat g)

theorem wd_norm_sq (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Formalism.REAL.UJ ε) :
    ‖wdF ε f g‖ ^ 2 = S7.hs (Formalism.MainNotions.S.umat g) * ‖f (Formalism.MainNotions.S.umat g)‖ ^ 2 := by
  have h0 : 0 ≤ S7.hs (Formalism.MainNotions.S.umat g) := by unfold S7.hs; positivity
  rw [wdF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt h0]

theorem wd_exp_hh (i : Fin n) (g : Formalism.REAL.UJ ε) :
    Real.exp (2 * (1 / 2 : ℝ) * Formalism.REAL.hh (Formalism.REAL.toM g)) = S7.hs (Formalism.MainNotions.S.umat g) := by
  have h1 : 1 ≤ S7.hs (Formalism.MainNotions.S.umat g) := sigZeroDecay_one_le_hs g.2 i
  rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num, one_mul]
  exact Real.exp_log (show 0 < Formalism.REAL.hs (Formalism.REAL.toM g) from lt_of_lt_of_le one_pos h1)

theorem wd_memLp_iff (i : Fin n) {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hc : Continuous (fun g : Formalism.REAL.UJ ε => f (Formalism.MainNotions.S.umat g))) :
    MemLp (wdF ε f) 2 (Formalism.REAL.muG ε) ↔
      Integrable (fun g => Real.exp (2 * (1 / 2 : ℝ) * Formalism.REAL.hh (Formalism.REAL.toM g)) * ‖f (Formalism.REAL.toM g)‖ ^ 2)
        (Formalism.REAL.muG ε) := by
  have hm : AEStronglyMeasurable (wdF ε f) (Formalism.REAL.muG ε) := by
    have : Continuous (wdF ε f) := by
      unfold wdF
      exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (wd_hs_cont.comp (continuous_umatA ε)))).mul hc
    exact this.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  have e : (fun g => ‖wdF ε f g‖ ^ 2) =
      fun g => Real.exp (2 * (1 / 2 : ℝ) * Formalism.REAL.hh (Formalism.REAL.toM g)) * ‖f (Formalism.REAL.toM g)‖ ^ 2 := by
    funext g
    rw [wd_norm_sq, wd_exp_hh i]
  rw [e]

end ReciprocityTheory.ChartRestriction.DS
