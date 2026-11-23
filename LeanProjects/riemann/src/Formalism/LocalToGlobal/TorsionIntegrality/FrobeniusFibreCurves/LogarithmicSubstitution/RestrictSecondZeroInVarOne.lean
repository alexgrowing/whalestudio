import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

namespace Formalism.L2.Th1.B.Add1

open Formalism.InvariantFactorPaths.G7 (at1)

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [CharZero K]

def at1H {ι : Type} (x : ι) : PowerSeries K →ₐ[K] MvPowerSeries ι K :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.X x)

theorem triple_lintegral_eq {ι : Type} (x : ι) (f : PowerSeries K) : at1 x f = at1H x f := by
  simp only [Formalism.InvariantFactorPaths.G7.at1, at1H, PowerSeries.coe_substAlgHom]

theorem inVarAlgHom_C {ι : Type} (x : ι) (c : K) :
    at1H x (PowerSeries.C c) = (MvPowerSeries.C c : MvPowerSeries ι K) := by
  rw [← triple_lintegral_eq]
  exact PowerSeries.subst_C c

def ev0H : MvPowerSeries (Fin 2) K →ₐ[K] PowerSeries K :=
  MvPowerSeries.substAlgHom (a := ![(PowerSeries.X : PowerSeries K), 0])
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (by
      intro i; fin_cases i
      · exact PowerSeries.constantCoeff_X
      · exact map_zero _))

theorem evalYZero_eq (h : MvPowerSeries (Fin 2) K) : ev0 h = ev0H h := by
  simp only [Formalism.L2.Th1.B.ev0, ev0H, MvPowerSeries.coe_substAlgHom]

theorem cc_psubst {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha f hf

theorem constantCoeff_inVar_eq_zero {ι : Type} (x : ι) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (at1 x f) = 0 :=
  cc_psubst (MvPowerSeries.constantCoeff_X x) hf

private theorem at1_mul {ι : Type} (x : ι) (f g : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.at1 x (f * g) = Formalism.InvariantFactorPaths.G7.at1 x f * Formalism.InvariantFactorPaths.G7.at1 x g := by
  simp only [triple_lintegral_eq, map_mul]

private theorem at1_X_eq_X {ι : Type} (x : ι) :
    Formalism.InvariantFactorPaths.G7.at1 x (PowerSeries.X : PowerSeries K) = MvPowerSeries.X x :=
  PowerSeries.subst_X (PowerSeries.HasSubst.X x)

private theorem ev0_mul (a b : MvPowerSeries (Fin 2) K) :
    Formalism.L2.Th1.B.ev0 (a * b) = Formalism.L2.Th1.B.ev0 a * Formalism.L2.Th1.B.ev0 b := by
  simp only [evalYZero_eq, map_mul]

private theorem ev0_X_one_eq_zero : Formalism.L2.Th1.B.ev0 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
  rw [evalYZero_eq, ev0H, MvPowerSeries.substAlgHom_X]
  rfl

theorem restrictSecondZero_inVar_one {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    ev0 (at1 1 f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [at1_mul, at1_X_eq_X, ev0_mul, ev0_X_one_eq_zero, zero_mul]

theorem partialDeriv_inVar_self (x : Fin 2) (f : PowerSeries K) : pd x (at1 x f) = at1 x (dz f) := by
  show MvPowerSeries.pderiv K x (PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) f) =
    PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) (PowerSeries.derivative K f)
  rw [Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X x) f x,
    MvPowerSeries.pderiv_X_self, mul_one]

theorem partialDeriv_inVar_of_ne {x y : Fin 2} (h : y ≠ x) (f : PowerSeries K) : pd x (at1 y f) = 0 := by
  show MvPowerSeries.pderiv K x (PowerSeries.subst (MvPowerSeries.X y : MvPowerSeries (Fin 2) K) f) = 0
  rw [Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X y) f x,
    MvPowerSeries.pderiv_X_of_ne h, mul_zero]

theorem pd_mul {ι : Type} (i : ι) (x y : MvPowerSeries ι K) :
    pd i (x * y) = x * pd i y + y * pd i x := by
  simp only [Formalism.L2.Th1.B.pd, Derivation.leibniz, smul_eq_mul]

theorem pd_sub {ι : Type} (i : ι) (x y : MvPowerSeries ι K) : pd i (x - y) = pd i x - pd i y :=
  map_sub (MvPowerSeries.pderiv K i) x y

theorem wave_alg {R : Type} [CommRing R] (k a u v u1 u2 v1 v2 p0 p1 q0 q1 P0 P1 : R)
    (hW : P0 - P1 = 2 * k * (u - v))
    (h0 : (1 - k * u * v) * p0 = -(k * u1 * v))
    (h0' : -(k * u1 * v) * p0 + (1 - k * u * v) * q0 = -(k * u2 * v))
    (h1 : (1 - k * u * v) * p1 = -(k * u * v1))
    (h1' : -(k * u * v1) * p1 + (1 - k * u * v) * q1 = -(k * u * v2))
    (E1u : u1 ^ 2 = 4 * u + 4 * a * u ^ 2 + 4 * k * u ^ 3)
    (E1v : v1 ^ 2 = 4 * v + 4 * a * v ^ 2 + 4 * k * v ^ 3)
    (E2u : u2 = 2 + 4 * a * u + 6 * k * u ^ 2)
    (E2v : v2 = 2 + 4 * a * v + 6 * k * v ^ 2) :
    (1 - k * u * v) ^ 2 * (P0 - q0) = (1 - k * u * v) ^ 2 * (P1 - q1) := by
  linear_combination (1 - k * u * v) ^ 2 * hW - (1 - k * u * v) * h0' - (k * u1 * v) * h0
    + (1 - k * u * v) * h1' + (k * u * v1) * h1 + ((1 - k * u * v) * k * v) * E2u
    - ((1 - k * u * v) * k * u) * E2v + (k ^ 2 * v ^ 2) * E1u - (k ^ 2 * u ^ 2) * E1v

private theorem ev0_sub (a b : MvPowerSeries (Fin 2) K) :
    Formalism.L2.Th1.B.ev0 (a - b) = Formalism.L2.Th1.B.ev0 a - Formalism.L2.Th1.B.ev0 b := by
  simp only [evalYZero_eq, map_sub]

private theorem ev0_neg (a : MvPowerSeries (Fin 2) K) :
    Formalism.L2.Th1.B.ev0 (-a) = -Formalism.L2.Th1.B.ev0 a := by
  simp only [evalYZero_eq, map_neg]

private theorem ev0_one : Formalism.L2.Th1.B.ev0 (1 : MvPowerSeries (Fin 2) K) = 1 := by
  simp only [evalYZero_eq, map_one]

private theorem pd_neg {ι : Type} (i : ι) (x : MvPowerSeries ι K) :
    Formalism.L2.Th1.B.pd i (-x) = -Formalism.L2.Th1.B.pd i x :=
  map_neg (MvPowerSeries.pderiv K i) x

private theorem pd_one_eq_zero {ι : Type} (i : ι) : Formalism.L2.Th1.B.pd i (1 : MvPowerSeries ι K) = 0 :=
  MvPowerSeries.pderiv_one

private theorem pd_C_eq_zero {ι : Type} (i : ι) (c : K) :
    Formalism.L2.Th1.B.pd i (MvPowerSeries.C c : MvPowerSeries ι K) = 0 :=
  MvPowerSeries.pderiv_C

private theorem pd_zero_C_mul_at1_mul_at1 (c : K) (F G : PowerSeries K) :
    Formalism.L2.Th1.B.pd (0 : Fin 2) (MvPowerSeries.C c * Formalism.InvariantFactorPaths.G7.at1 0 F * Formalism.InvariantFactorPaths.G7.at1 1 G) =
      MvPowerSeries.C c * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz F) * Formalism.InvariantFactorPaths.G7.at1 1 G := by
  rw [pd_mul, pd_mul, partialDeriv_inVar_self,
    partialDeriv_inVar_of_ne (show (1 : Fin 2) ≠ 0 by decide), pd_C_eq_zero]
  ring

private theorem pd_one_C_mul_at1_mul_at1 (c : K) (F G : PowerSeries K) :
    Formalism.L2.Th1.B.pd (1 : Fin 2) (MvPowerSeries.C c * Formalism.InvariantFactorPaths.G7.at1 0 F * Formalism.InvariantFactorPaths.G7.at1 1 G) =
      MvPowerSeries.C c * Formalism.InvariantFactorPaths.G7.at1 0 F * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz G) := by
  rw [pd_mul, pd_mul, partialDeriv_inVar_self,
    partialDeriv_inVar_of_ne (show (0 : Fin 2) ≠ 1 by decide), pd_C_eq_zero]
  ring

private theorem pd_zero_one_sub_C_mul_at1_mul_at1 (kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.pd (0 : Fin 2) (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz w) * Formalism.InvariantFactorPaths.G7.at1 1 w) := by
  rw [pd_sub, pd_one_eq_zero, pd_zero_C_mul_at1_mul_at1]
  ring

private theorem pd_one_one_sub_C_mul_at1_mul_at1 (kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.pd (1 : Fin 2) (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz w)) := by
  rw [pd_sub, pd_one_eq_zero, pd_one_C_mul_at1_mul_at1]
  ring

private theorem pd_zero_pd_zero_one_sub_C_mul_at1_mul_at1 (kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.pd (0 : Fin 2) (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w)) * Formalism.InvariantFactorPaths.G7.at1 1 w) := by
  rw [pd_zero_one_sub_C_mul_at1_mul_at1, pd_neg, pd_zero_C_mul_at1_mul_at1]

private theorem pd_one_pd_one_one_sub_C_mul_at1_mul_at1 (kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.pd (1 : Fin 2) (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w))) := by
  rw [pd_one_one_sub_C_mul_at1_mul_at1, pd_neg, pd_one_C_mul_at1_mul_at1]

private theorem constantCoeff_one_sub_C_mul_at1_mul_at1 {kap : K} {w : PowerSeries K}
    (hw0 : PowerSeries.constantCoeff w = 0) :
    MvPowerSeries.constantCoeff ((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K) = 1 := by
  rw [map_sub, map_one, map_mul, map_mul, constantCoeff_inVar_eq_zero (0 : Fin 2) hw0]
  simp

private theorem constantCoeff_sig1S_eq_zero (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.constantCoeff (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Formalism.L2.Th1.B.sigmaOneSeries, Formalism.L2.Th1.B.prim]

private theorem coeff_one_sig1S_eq_zero (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.coeff 1 (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w) = 0 := by
  simp [Formalism.L2.Th1.B.sigmaOneSeries, Formalism.L2.Th1.B.prim]

private theorem dz_dz_sig1S_eq_neg_C_add_C_mul (h4 : Formalism.L2.Th1.B.PrimRules) (e1 kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w)) = -(PowerSeries.C e1 + PowerSeries.C kap * w) := by
  have hp : ∀ f : PowerSeries K, PowerSeries.derivative K (Formalism.L2.Th1.B.prim f) = f := fun f => (h4 K f).1
  show PowerSeries.derivative K (PowerSeries.derivative K
      (-Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (PowerSeries.C e1 + PowerSeries.C kap * w)))) = _
  rw [Derivation.map_neg, Derivation.map_neg, hp, hp]

private theorem at1_neg_C_add_C_mul {ι : Type} (e1 kap : K) (w : PowerSeries K) (x : ι) :
    Formalism.InvariantFactorPaths.G7.at1 x (-(PowerSeries.C e1 + PowerSeries.C kap * w)) =
      -(MvPowerSeries.C e1 + MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 x w) := by
  simp only [triple_lintegral_eq, map_neg, map_add, map_mul, inVarAlgHom_C]

private theorem at1_dz_sq_eq_cubic {A kap : K} {w : PowerSeries K}
    (hw : Formalism.L2.Th1.B.dz w ^ 2 = 4 * w + 4 * PowerSeries.C A * w ^ 2 + 4 * PowerSeries.C kap * w ^ 3)
    (x : Fin 2) :
    Formalism.InvariantFactorPaths.G7.at1 x (Formalism.L2.Th1.B.dz w) ^ 2 = 4 * Formalism.InvariantFactorPaths.G7.at1 x w + 4 * MvPowerSeries.C A * Formalism.InvariantFactorPaths.G7.at1 x w ^ 2 +
      4 * MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 x w ^ 3 := by
  have h := congrArg (at1H (K := K) x) hw
  simp only [map_add, map_mul, map_pow, map_ofNat, inVarAlgHom_C] at h
  simp only [triple_lintegral_eq]
  exact h

private theorem at1_dz_dz_eq_quadratic {A kap : K} {w : PowerSeries K}
    (hw : Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w) = 2 + 4 * PowerSeries.C A * w + 6 * PowerSeries.C kap * w ^ 2)
    (x : Fin 2) :
    Formalism.InvariantFactorPaths.G7.at1 x (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w)) = 2 + 4 * MvPowerSeries.C A * Formalism.InvariantFactorPaths.G7.at1 x w +
      6 * MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 x w ^ 2 := by
  rw [hw]
  simp only [triple_lintegral_eq, map_add, map_mul, map_pow, map_ofNat, inVarAlgHom_C]

theorem fLog_one (h1 : ExpLogRules) {ι : Type} : fLog (1 : MvPowerSeries ι K) = 0 := by
  obtain ⟨hA, hB, -⟩ := h1 K ι
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries ι K) = 0 := map_zero _
  have hsq : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) * Formalism.L2.Th1.B.fExp 0 = Formalism.L2.Th1.B.fExp 0 * 1 := by
    rw [← hA 0 0 h0 h0, add_zero, mul_one]
  have hu : IsUnit (Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K)) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [(hB 0 h0).1]; exact isUnit_one)
  have he : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) = 1 := hu.mul_left_cancel hsq
  have hl := (hB 0 h0).2
  rw [he] at hl
  exact hl

end SlopeTestRemainingChoices

set_option maxHeartbeats 800000 in

theorem AddSigma1Log_of (h1 : ExpLogRules) (h2 : ExpLogDeriv) (h3 : ExpLogSubst) (h4 : PrimRules)
    (h5 : WaveUnique) (h6 : WaveKills) (h7 : ParCauchy) (h8 : WSecond) : AddSigma1Log := by
  unfold Formalism.L2.Th1.B.AddSigma1Log
  intro K _ _ A kap e1 w hw
  have hw0 : PowerSeries.constantCoeff w = 0 := hw.1
  obtain ⟨hw1, hw2⟩ := h8 K A kap w hw
  have hwd0 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.dz w) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp [hw1]
  have hL0 := constantCoeff_sig1S_eq_zero e1 kap w
  have hL1 := coeff_one_sig1S_eq_zero e1 kap w
  have hL2 := dz_dz_sig1S_eq_neg_C_add_C_mul h4 e1 kap w
  obtain ⟨hC0, hC1⟩ := h7 K _ hL0 hL1
  have hg : MvPowerSeries.constantCoeff ((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K) = 1 :=
    constantCoeff_one_sub_C_mul_at1_mul_at1 hw0
  have hW : Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.par0 (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w))) -
      Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.par0 (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w))) =
      2 * MvPowerSeries.C kap * (Formalism.InvariantFactorPaths.G7.at1 0 w - Formalism.InvariantFactorPaths.G7.at1 1 w) := by
    rw [h6 K, hL2, at1_neg_C_add_C_mul, at1_neg_C_add_C_mul]
    ring
  have hd0 := (h2 K (Fin 2) 0).2 _ hg
  have hd1 := (h2 K (Fin 2) 1).2 _ hg
  have e0 : (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) * Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz w) * Formalism.InvariantFactorPaths.G7.at1 1 w) :=
    hd0.trans (pd_zero_one_sub_C_mul_at1_mul_at1 kap w)
  have e1' : (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) * Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz w)) :=
    hd1.trans (pd_one_one_sub_C_mul_at1_mul_at1 kap w)
  have f0 : -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz w) * Formalism.InvariantFactorPaths.G7.at1 1 w) *
        Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) +
      (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) * Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w))) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w)) * Formalism.InvariantFactorPaths.G7.at1 1 w) := by
    have t := congrArg (Formalism.L2.Th1.B.pd (0 : Fin 2)) hd0
    rw [pd_mul, pd_zero_pd_zero_one_sub_C_mul_at1_mul_at1, pd_zero_one_sub_C_mul_at1_mul_at1] at t
    linear_combination t
  have f1 : -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz w)) *
        Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) +
      (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) * Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w))) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w))) := by
    have t := congrArg (Formalism.L2.Th1.B.pd (1 : Fin 2)) hd1
    rw [pd_mul, pd_one_pd_one_one_sub_C_mul_at1_mul_at1, pd_one_one_sub_C_mul_at1_mul_at1] at t
    linear_combination t
  have hsq := wave_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW e0 f0 e1' f1
    (at1_dz_sq_eq_cubic hw.2.2 0) (at1_dz_sq_eq_cubic hw.2.2 1)
    (at1_dz_dz_eq_quadratic hw2 0) (at1_dz_dz_eq_quadratic hw2 1)
  have hu : IsUnit (((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K) ^ 2) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [map_pow, hg, one_pow]; exact isUnit_one)
  have hwave := hu.mul_left_cancel hsq
  have hRg : Formalism.L2.Th1.B.ev0 ((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K) = 1 := by
    rw [ev0_sub, ev0_one, ev0_mul, restrictSecondZero_inVar_one hw0, mul_zero, sub_zero]
  have hRl : Formalism.L2.Th1.B.ev0 (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) = 0 := by
    have hφ : ∀ i, MvPowerSeries.constantCoeff
        ((![(PowerSeries.X : PowerSeries K), 0] : Fin 2 → PowerSeries K) i) = 0 := by
      intro i; fin_cases i
      · exact PowerSeries.constantCoeff_X
      · exact map_zero _
    have e : Formalism.L2.Th1.B.ev0 (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.ev0 ((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K)) :=
      (h3 K (Fin 2) Unit ![(PowerSeries.X : PowerSeries K), 0] hφ).2 _ hg
    rw [e, hRg]
    exact fLog_one h1
  have hRp : Formalism.L2.Th1.B.ev0 (Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w))) = 0 := by
    have t := congrArg Formalism.L2.Th1.B.ev0 hd1
    rw [ev0_mul, hRg, one_mul, pd_one_one_sub_C_mul_at1_mul_at1, ev0_neg, ev0_mul,
      restrictSecondZero_inVar_one hwd0, mul_zero, neg_zero] at t
    exact t
  have hfin : (Formalism.L2.Th1.B.par0 (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w)) - (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) = 0 := by
    apply h5 K
    · simp only [pd_sub]
      exact hwave
    · rw [ev0_sub, hC0, hRl, sub_zero]
    · rw [pd_sub, ev0_sub, hC1, hRp, sub_zero]
  exact sub_eq_zero.mp hfin

end Formalism.L2.Th1.B.Add1
