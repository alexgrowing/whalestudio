import Formalism.EllipticTorsion.Statement
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

noncomputable section

open PowerSeries

universe u

namespace Formalism.ELL.PadicMultiplication

open Formalism.G Formalism.G.LogP

section Ring

variable {R : Type*} [CommRing R]

def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | m + 1 => MvPowerSeries.subst (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries

theorem mulN_zero (F : FormalGroup R) : mulN F 0 = 0 := rfl

theorem mulN_succ (F : FormalGroup R) (m : ℕ) :
    mulN F (m + 1) = MvPowerSeries.subst
      (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries := rfl

theorem constantCoeff_mulN (F : FormalGroup R) (m : ℕ) :
    MvPowerSeries.constantCoeff (mulN F m) = 0 := by
  induction m with
  | zero => simp [mulN_zero]
  | succ m ih =>
    rw [mulN_succ]
    have := constantCoeff_subst_of_zero (R := R) F.toPowerSeries
      (b := (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R))
      (fun i => by fin_cases i; exacts [ih, PowerSeries.constantCoeff_X])
    rw [F.zero_constantCoeff] at this
    exact this

end Ring

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem map_mulN (F : FormalGroup (unitBall K)) (m : ℕ) :
    (mulN F (m + 1)).map (unitBall K).subtype =
      MvPowerSeries.subst
        (![(mulN F m).map (unitBall K).subtype, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K)
        (F.map (unitBall K).subtype).toPowerSeries := by
  rw [mulN_succ]
  have hs := hs2 (R := unitBall K) (constantCoeff_mulN F m)
    (u := mulN F m) (v := (PowerSeries.X : PowerSeries (unitBall K))) PowerSeries.constantCoeff_X
  rw [PowerSeries.map, MvPowerSeries.map_subst hs]
  simp only [FormalGroup.map_toPowerSeries]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact PowerSeries.map_X _

theorem log_mulN (F : FormalGroup (unitBall K)) (l : PowerSeries K)
    (hl : IsLog (F.map (unitBall K).subtype) l) (m : ℕ) :
    l.subst ((mulN F m).map (unitBall K).subtype) = (m : K) • l := by
  obtain ⟨hl0, -, hlF⟩ := hl
  induction m with
  | zero => simp [mulN_zero, hl0]
  | succ m ih =>
    have hM : MvPowerSeries.constantCoeff ((mulN F m).map (unitBall K).subtype) = 0 := by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (mulN F m)) = 0
      rw [MvPowerSeries.constantCoeff_map, constantCoeff_mulN]; simp
    have hs := hs2 (R := K) hM (v := (PowerSeries.X : PowerSeries K)) PowerSeries.constantCoeff_X
    rw [map_mulN, ← psubst_subst l (F.map (unitBall K).subtype).zero_constantCoeff hs, hlF,
      MvPowerSeries.subst_add hs, atX, atY,
      psubst_subst l (by simp) hs, psubst_subst l (by simp) hs,
      MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ih, PowerSeries.X_subst]
    push_cast
    rw [add_smul, one_smul]

end Formalism.ELL.PadicMultiplication

namespace Formalism.ELL.PadicMultiplication

open Formalism.G Formalism.G.LogP

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem e_natMul (F : FormalGroup (unitBall K)) (l e : PowerSeries K)
    (hl : IsLog (F.map (unitBall K).subtype) l) (hel : e.subst l = X) (m : ℕ) :
    e.subst ((m : K) • l) = (mulN F m).map (unitBall K).subtype := by
  have hM : MvPowerSeries.constantCoeff ((mulN F m).map (unitBall K).subtype) = 0 := by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (mulN F m)) = 0
    rw [MvPowerSeries.constantCoeff_map, constantCoeff_mulN]; simp
  rw [← log_mulN F l hl m, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hl.1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hM), hel,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hM)]

theorem integral_natMul (F : FormalGroup (unitBall K)) (m n : ℕ) :
    ‖coeff n ((mulN F m).map (unitBall K).subtype)‖ ≤ 1 := by
  rw [PowerSeries.coeff_map]
  exact (coeff n (mulN F m)).2

def coeffPoly (l e : PowerSeries K) (n : ℕ) : Polynomial K :=
  ∑ d ∈ Finset.range (n + 1),
    Polynomial.C (coeff d e * coeff n (l ^ d)) * Polynomial.X ^ d

theorem coeff_subst_smul (l e : PowerSeries K) (hl0 : constantCoeff l = 0) (c : K) (n : ℕ) :
    coeff n (e.subst (c • l)) = (coeffPoly l e n).eval c := by
  have hcl : constantCoeff (c • l) = 0 := by simp [hl0]
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hl0
  have hz : ∀ d, n < d → coeff n (l ^ d) = 0 := by
    intro d hd
    rw [hg, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hcl),
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · simp only [coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, smul_pow, PowerSeries.coeff_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun d _ => by ring
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hd
    rw [smul_pow, PowerSeries.coeff_smul, hz d (by omega), smul_zero, smul_zero]

end Formalism.ELL.PadicMultiplication

namespace Formalism.ELL

open Formalism.G Formalism.ELL.PadicMultiplication

theorem padicMult_of (h : IntValuedZp.{u}) : PadicMult.{u} := by
  intro p _ K _ _ _ F l e hl he0 hel hle b n
  rw [coeff_subst_smul l e hl.1]
  refine h p K (coeffPoly l e n) (fun m => ?_) b
  rw [← coeff_subst_smul l e hl.1, e_natMul F l e hl hel m]
  exact integral_natMul F m n

end Formalism.ELL
