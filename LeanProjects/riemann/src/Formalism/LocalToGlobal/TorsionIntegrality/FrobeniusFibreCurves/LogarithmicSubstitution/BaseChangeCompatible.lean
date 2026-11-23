import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementC

noncomputable section

namespace Formalism.L2.Th1.B.Map

open Formalism.InvariantFactorPaths.G7 (at1 cob)

variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')

theorem map_psubst {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.map j a) (PowerSeries.map j f) := by
  have ha' : MvPowerSeries.constantCoeff (MvPowerSeries.map j a) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, ha, map_zero]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero ha'
  ext e
  rw [MvPowerSeries.coeff_map, PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs',
    map_finsum j (PowerSeries.coeff_subst_finite hs f e)]
  refine finsum_congr fun d => ?_
  rw [smul_eq_mul, smul_eq_mul, map_mul, PowerSeries.coeff_map, ← map_pow (MvPowerSeries.map j),
    MvPowerSeries.coeff_map]

theorem map_psubst' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    PowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (PowerSeries.map j a) (PowerSeries.map j f) :=
  map_psubst j (ι := Unit) ha f

theorem map_fExp {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.map j (fExp a) = fExp (MvPowerSeries.map j a) := by
  unfold Formalism.L2.Th1.B.fExp
  rw [map_psubst j ha, PowerSeries.map_exp]

theorem map_fExp' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.map j (fExp a) = fExp (PowerSeries.map j a) :=
  map_fExp j (ι := Unit) ha

theorem map_fLog {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 1) :
    MvPowerSeries.map j (fLog a) = fLog (MvPowerSeries.map j a) := by
  have h' : MvPowerSeries.constantCoeff (a - 1) = 0 := by rw [map_sub, ha, map_one, sub_self]
  unfold Formalism.L2.Th1.B.fLog
  rw [map_psubst j h', map_sub, map_one, PowerSeries.map_log]

theorem map_fLog' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 1) :
    PowerSeries.map j (fLog a) = fLog (PowerSeries.map j a) :=
  map_fLog j (ι := Unit) ha

theorem map_prim (f : PowerSeries K) :
    PowerSeries.map j (prim f) = prim (PowerSeries.map j f) := by
  ext n
  simp only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_div₀, map_natCast]

theorem map_lU (l : PowerSeries K) :
    PowerSeries.map j (lU l) = lU (PowerSeries.map j l) := by
  ext n
  simp only [Formalism.L2.Th1.B.lU, PowerSeries.coeff_map, PowerSeries.coeff_mk]

private theorem powerSeries_constantCoeff_map' (f : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.map j f) = j (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map]

theorem map_inv' {f : PowerSeries K} (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.map j f⁻¹ = (PowerSeries.map j f)⁻¹ := by
  have h' : PowerSeries.constantCoeff (PowerSeries.map j f) ≠ 0 := by
    rw [powerSeries_constantCoeff_map']; exact (map_ne_zero j).mpr hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one h', ← map_mul, PowerSeries.inv_mul_cancel _ hf, map_one]

theorem map_sigS (P : PowerSeries K) :
    PowerSeries.map j (sigS P) = sigS (PowerSeries.map j P) := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, map_prim, map_prim]

theorem cc_sigS (P : PowerSeries K) : PowerSeries.constantCoeff (sigS P) = 0 := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]

theorem map_sig1S (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigmaOneSeries e1 kap w) = sigmaOneSeries (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, map_prim, map_prim, map_add, map_mul, PowerSeries.map_C,
    PowerSeries.map_C]

theorem cc_sig1S (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]

theorem map_sigma (P : PowerSeries K) :
    PowerSeries.map j (sigma P) = sigma (PowerSeries.map j P) := by
  unfold Formalism.L2.Th1.B.sigma
  rw [map_mul, PowerSeries.map_X, map_fExp' j (cc_sigS P),
    map_sigS]

theorem map_sgStar (s2 : K) (P : PowerSeries K) :
    PowerSeries.map j (sgStar s2 P) = sgStar (j s2) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) = 0 := by
    simp
  unfold Formalism.L2.Th1.B.sgStar
  rw [map_mul, map_sigma, map_fExp' j hc, map_neg, map_mul, PowerSeries.map_C,
    map_pow, PowerSeries.map_X, map_div₀, map_ofNat]

theorem map_sigma1 (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigma1 e1 kap w) = sigma1 (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigma1
  rw [map_fExp' j (cc_sig1S e1 kap w), map_sig1S]

theorem map_wOf (e1 : K) (P : PowerSeries K) :
    PowerSeries.map j (wOf e1 P) = wOf (j e1) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) ≠ 0 := by
    simp
  unfold Formalism.L2.Th1.B.wOf
  rw [map_mul, map_inv' j hc]
  simp only [map_pow, map_sub, map_add, map_one, map_mul, PowerSeries.map_X, PowerSeries.map_C]

theorem map_phO (s2 : K) (P : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.map j (phO s2 P l) = phO (j s2) (PowerSeries.map j P) (PowerSeries.map j l) := by
  have hd : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.B.lU, PowerSeries.coeff_mk, zero_add, h1]
  unfold Formalism.L2.Th1.B.phO
  rw [map_sub, map_add, map_neg, map_psubst' j h0, map_sigS, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow, map_fLog' j hd, map_lU]

theorem map_phE (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) :
    PowerSeries.map j (phE s2 e1 kap w l) =
      phE (j s2) (j e1) (j kap) (PowerSeries.map j w) (PowerSeries.map j l) := by
  unfold Formalism.L2.Th1.B.phE
  rw [map_add, map_neg, map_psubst' j h0, map_sig1S, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow]

theorem map_inVar {ι : Type} (x : ι) (f : PowerSeries K) :
    MvPowerSeries.map j (at1 x f) = at1 x (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.at1
  rw [map_psubst j (MvPowerSeries.constantCoeff_X x), MvPowerSeries.map_X]

theorem map_cob {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (cob F f) = cob (MvPowerSeries.map j F) (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.cob
  rw [map_sub, map_sub, map_psubst j hF, map_inVar, map_inVar]

theorem baseChangeCompatible : BaseChange := by
  intro K K' _ _ _ _ j s2 e1 kap P w l F h0 h1 hF
  exact ⟨map_sigma j P, map_sgStar j s2 P, map_sigma1 j e1 kap w,
    map_wOf j e1 P, map_phO j s2 P h0 h1,
    map_phE j s2 e1 kap w h0, fun f => map_cob j hF f⟩

end Formalism.L2.Th1.B.Map
