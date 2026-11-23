import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst

noncomputable section

namespace Formalism.L2.Th1.B.ParO

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem fExp_zero {ι : Type} : fExp (0 : MvPowerSeries ι K) = 1 := by
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries ι K) = 0 := map_zero _
  have hm : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) * Formalism.L2.Th1.B.fExp 0 = Formalism.L2.Th1.B.fExp 0 * 1 := by
    rw [mul_one, ← Formalism.L2.Th1.B.fExp_add h0 h0, add_zero]
  have hne : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) ≠ 0 := by
    intro h
    have h1 := Formalism.L2.Th1.B.constantCoeff_fExp h0
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne hm

theorem fExp_mul_neg {ι : Type} {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    fExp f * fExp (-f) = 1 := by
  have hnf : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
  rw [← Formalism.L2.Th1.B.fExp_add hf hnf, add_neg_cancel, fExp_zero]

theorem fLog_mul {ι : Type} {g h : MvPowerSeries ι K} (hg : MvPowerSeries.constantCoeff g = 1)
    (hh : MvPowerSeries.constantCoeff h = 1) : fLog (g * h) = fLog g + fLog h := by
  have hg0 := Formalism.L2.Th1.B.constantCoeff_fLog hg
  have hh0 := Formalism.L2.Th1.B.constantCoeff_fLog hh
  have hs : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.fLog g + Formalism.L2.Th1.B.fLog h) = 0 := by
    rw [map_add, hg0, hh0, add_zero]
  calc Formalism.L2.Th1.B.fLog (g * h) = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog g) * Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog h)) := by
        rw [Formalism.L2.Th1.B.fExp_fLog hg, Formalism.L2.Th1.B.fExp_fLog hh]
    _ = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog g + Formalism.L2.Th1.B.fLog h)) := by rw [Formalism.L2.Th1.B.fExp_add hg0 hh0]
    _ = Formalism.L2.Th1.B.fLog g + Formalism.L2.Th1.B.fLog h := Formalism.L2.Th1.B.fLog_fExp hs

theorem subst_inVar {ι κ : Type} (f : PowerSeries K) (x : ι) {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X x : MvPowerSeries ι K) = 0 := by simp
  rw [Formalism.InvariantFactorPaths.G7.at1, Formalism.L2.Th1.B.psubst_msubst f hX hb, MvPowerSeries.subst_X hb]

theorem constantCoeff_inVar {ι : Type} (x : ι) {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (at1 x f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf

theorem psubst_fExp {ι : Type} {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst u (fExp f) = fExp (PowerSeries.subst u f) := by
  simp only [Formalism.L2.Th1.B.fExp]
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
    (PowerSeries.HasSubst.of_constantCoeff_zero hu) _

theorem psubst_neg {ι : Type} {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0)
    (f : PowerSeries K) : PowerSeries.subst u (-f) = -PowerSeries.subst u f := by
  rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hu), map_neg]

theorem value_at {ι : Type} {l g ph : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hph : PowerSeries.constantCoeff ph = 0)
    (e : PowerSeries.subst l g = PowerSeries.X * fExp (-ph))
    {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst (PowerSeries.subst U l) g = U * fExp (-PowerSeries.subst U ph) := by
  have hlS := PowerSeries.HasSubst.of_constantCoeff_zero' hl
  have hUS := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hnph : PowerSeries.constantCoeff (-ph) = 0 := by rw [map_neg, hph, neg_zero]
  rw [← PowerSeries.subst_comp_subst_apply hlS hUS, e, PowerSeries.subst_mul hUS,
    PowerSeries.subst_X hUS, psubst_fExp hU hnph, psubst_neg hU]

theorem inVar_ne_zero {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) (x : Fin 2) :
    at1 x l ≠ 0 := by
  intro h
  have h2 := congrArg (fun φ => MvPowerSeries.coeff (Finsupp.single x 1) φ) h
  simp only [Formalism.InvariantFactorPaths.G7.at1, map_zero, PowerSeries.coeff_subst_single] at h2
  simp [hl1] at h2

theorem inVar_add_inVar_ne_zero {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) :
    at1 (0 : Fin 2) l + at1 1 l ≠ 0 := by
  intro h
  have h2 := congrArg (fun φ => MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) φ) h
  simp only [Formalism.InvariantFactorPaths.G7.at1, map_add, map_zero, PowerSeries.coeff_subst_single] at h2
  simp [hl1] at h2

theorem inVar_sub_inVar_ne_zero {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) :
    at1 (0 : Fin 2) l - at1 1 l ≠ 0 := by
  intro h
  have h2 := congrArg (fun φ => MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) φ) h
  simp only [Formalism.InvariantFactorPaths.G7.at1, map_sub, map_zero, PowerSeries.coeff_subst_single] at h2
  simp [hl1] at h2

theorem ne_zero_of_psubst {ι : Type} {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    {U : MvPowerSeries ι K} (h : PowerSeries.subst U l ≠ 0) : U ≠ 0 := by
  rintro rfl
  exact h (PowerSeries.subst_zero_of_constantCoeff_zero hl)

theorem subst_atS {ι : Type} (g : PowerSeries K) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (atS g) = PowerSeries.subst (b 0 + b 1) g := by
  have h0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  rw [Formalism.L2.Th1.B.atS, Formalism.L2.Th1.B.psubst_msubst g h0 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]

theorem subst_atD {ι : Type} (g : PowerSeries K) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (atD g) = PowerSeries.subst (b 0 - b 1) g := by
  have h0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  rw [Formalism.L2.Th1.B.atD, Formalism.L2.Th1.B.psubst_msubst g h0 hb, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]

theorem subst_wpDiff {ι : Type} (P : PowerSeries K) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (wpDiff P) =
      b 0 ^ 2 - b 1 ^ 2 +
        b 0 ^ 2 * b 1 ^ 2 * (PowerSeries.subst (b 1) P - PowerSeries.subst (b 0) P) := by
  rw [Formalism.L2.Th1.B.wpDiff]
  simp only [MvPowerSeries.subst_add hb, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_mul hb,
    MvPowerSeries.subst_pow hb, MvPowerSeries.subst_X hb, subst_inVar P 0 hb, subst_inVar P 1 hb]

private theorem constantCoeff_vec_pair_eq_zero {ι : Type} {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    ∀ s : Fin 2, MvPowerSeries.constantCoeff (![a, b] s) = 0 :=
  Fin.forall_fin_two.mpr ⟨ha, hb⟩

theorem curve_at {ι : Type} {l P ep : PowerSeries K} {c0 : K}
    (hl : PowerSeries.constantCoeff l = 0)
    (h : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) (x : ι) :
    MvPowerSeries.X x ^ 2 * (1 + at1 x l ^ 2 * PowerSeries.subst (at1 x l) P) =
      at1 x l ^ 2 * (at1 x ep + MvPowerSeries.C c0 * MvPowerSeries.X x ^ 2) := by
  have hX : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have hlS := PowerSeries.HasSubst.of_constantCoeff_zero' hl
  have h2 := congrArg (fun φ : PowerSeries K => PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) φ) h
  simp only [PowerSeries.subst_mul hX, PowerSeries.subst_add hX, PowerSeries.subst_pow hX,
    Formalism.L2.Th1.B.psubst_one hX, PowerSeries.subst_X hX, PowerSeries.subst_C,
    PowerSeries.subst_comp_subst_apply hlS hX] at h2
  exact h2

end Alg

section Norm

variable {K : Type} [NormedField K] [CharZero K]

theorem log_law {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) :
    PowerSeries.subst F l = at1 0 l + at1 1 l := by
  have h5 := h.2.2.2.2
  simp only [Formalism.InvariantFactorPaths.G7.cob] at h5
  linear_combination h5

theorem constantCoeff_FI {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) : MvPowerSeries.constantCoeff (FI F i) = 0 := by
  have h1 : MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 1 i : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_inVar 1 hi.1
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vec_pair_eq_zero h0 h1))
    (constantCoeff_vec_pair_eq_zero h0 h1) h.1

theorem log_FI {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) : PowerSeries.subst (FI F i) l = at1 0 l - at1 1 l := by
  have h1 : MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 1 i : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_inVar 1 hi.1
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX1c : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hb : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 i] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vec_pair_eq_zero h0 h1)
  have hiS := PowerSeries.HasSubst.of_constantCoeff_zero' hi.1
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := PowerSeries.HasSubst.X 1
  rw [Formalism.L2.Th1.B.FI, ← Formalism.L2.Th1.B.psubst_msubst l h.1 hb, log_law h, MvPowerSeries.subst_add hb,
    subst_inVar l 0 hb, subst_inVar l 1 hb]
  show PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l
      + PowerSeries.subst (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) i) l
      = PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l
        - PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l
  rw [← PowerSeries.subst_comp_subst_apply hiS hX1, hi.2.2, psubst_neg hX1c l, sub_eq_add_neg]

private theorem addition_identity_products_eq_neg_c_mul_sq {R : Type} [CommRing R] [NoZeroDivisors R]
    {L0 L1 X0 X1 F D c EF ED E0 E1 P0 P1 ep0 ep1 c0 : R}
    (hN : L0 ^ 2 * L1 ^ 2 * F * D ≠ 0)
    (KE : L0 ^ 2 * L1 ^ 2 * (F * EF * (D * ED)) =
      (X0 * E0) ^ 2 * (X1 * E1) ^ 2 * (L0 ^ 2 - L1 ^ 2 + L0 ^ 2 * L1 ^ 2 * (P1 - P0)))
    (C0 : X0 ^ 2 * (1 + L0 ^ 2 * P0) = L0 ^ 2 * (ep0 + c0 * X0 ^ 2))
    (C1 : X1 ^ 2 * (1 + L1 ^ 2 * P1) = L1 ^ 2 * (ep1 + c0 * X1 ^ 2))
    (hc : X1 ^ 2 * ep0 - X0 ^ 2 * ep1 = c * F * D) :
    EF * ED = -c * E0 ^ 2 * E1 ^ 2 := by
  have W : X0 ^ 2 * X1 ^ 2 * (L0 ^ 2 - L1 ^ 2 + L0 ^ 2 * L1 ^ 2 * (P1 - P0)) =
      -(L0 ^ 2 * L1 ^ 2 * c * F * D) := by
    linear_combination (-(L0 ^ 2 * L1 ^ 2)) * hc + (X0 ^ 2 * L0 ^ 2) * C1 - (X1 ^ 2 * L1 ^ 2) * C0
  apply mul_left_cancel₀ hN
  linear_combination KE + (E0 ^ 2 * E1 ^ 2) * W

theorem par_eq (hA : AddSgStar) (hD : PhODef) {g2 g3 s2 c0 : K} {P l i ep : PowerSeries K}
    {F c : MvPowerSeries (Fin 2) K} (hP : IsWp g2 g3 P) (hF : LawLog F l) (hi : IsInv l i)
    (h3 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2))
    (hc : MvPowerSeries.X 1 ^ 2 * at1 0 ep - MvPowerSeries.X 0 ^ 2 * at1 1 ep = c * F * FI F i) :
    par F i (phO s2 P l) = -fLog (-c) := by
  have hl0 : PowerSeries.constantCoeff l = 0 := hF.2.2.1
  have hl1 : PowerSeries.coeff 1 l = 1 := hF.2.2.2.1
  have hF0 : MvPowerSeries.constantCoeff F = 0 := hF.1
  have hD0 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.FI F i) = 0 := constantCoeff_FI hF hi
  obtain ⟨hψ0, e⟩ := hD K s2 P l hl0 hl1
  have hAd := hA K g2 g3 s2 P hP
  have hL0c : MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_inVar 0 hl0
  have hL1c : MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 1 l : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_inVar 1 hl0
  have hb : MvPowerSeries.HasSubst ![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vec_pair_eq_zero hL0c hL1c)
  have hb0 : (![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] : Fin 2 → MvPowerSeries (Fin 2) K) 0 =
      Formalism.InvariantFactorPaths.G7.at1 0 l := rfl
  have hb1 : (![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] : Fin 2 → MvPowerSeries (Fin 2) K) 1 =
      Formalism.InvariantFactorPaths.G7.at1 1 l := rfl
  have KE := congrArg
    (fun φ => MvPowerSeries.subst ![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] φ) hAd
  simp only [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_pow hb, MvPowerSeries.subst_X hb,
    subst_atS (Formalism.L2.Th1.B.sgStar s2 P) hb, subst_atD (Formalism.L2.Th1.B.sgStar s2 P) hb,
    subst_inVar (Formalism.L2.Th1.B.sgStar s2 P) 0 hb, subst_inVar (Formalism.L2.Th1.B.sgStar s2 P) 1 hb,
    subst_wpDiff P hb, hb0, hb1] at KE
  have sF := value_at hl0 hψ0 e hF0
  have sD := value_at hl0 hψ0 e hD0
  have s0 : PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) (Formalism.L2.Th1.B.sgStar s2 P) =
      MvPowerSeries.X 0 * Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)) :=
    value_at hl0 hψ0 e (U := MvPowerSeries.X 0) (by simp)
  have s1 : PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 1 l : MvPowerSeries (Fin 2) K) (Formalism.L2.Th1.B.sgStar s2 P) =
      MvPowerSeries.X 1 * Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l)) :=
    value_at hl0 hψ0 e (U := MvPowerSeries.X 1) (by simp)
  rw [← log_law hF, ← log_FI hF hi, sF, sD, s0, s1] at KE
  have C0 := curve_at (ι := Fin 2) hl0 h3 0
  have C1 := curve_at (ι := Fin 2) hl0 h3 1
  have hL0 := inVar_ne_zero hl1 0
  have hL1 := inVar_ne_zero hl1 1
  have hFne : F ≠ 0 := ne_zero_of_psubst hl0
    (by rw [log_law hF]; exact inVar_add_inVar_ne_zero hl1)
  have hDne : Formalism.L2.Th1.B.FI F i ≠ 0 := ne_zero_of_psubst hl0
    (by rw [log_FI hF hi]; exact inVar_sub_inVar_ne_zero hl1)
  have hN : (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) ^ 2 * Formalism.InvariantFactorPaths.G7.at1 1 l ^ 2 * F * Formalism.L2.Th1.B.FI F i ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hL0) (pow_ne_zero 2 hL1)) hFne) hDne
  have hEE := addition_identity_products_eq_neg_c_mul_sq
    (L0 := (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K)) (L1 := Formalism.InvariantFactorPaths.G7.at1 1 l)
    (X0 := MvPowerSeries.X 0) (X1 := MvPowerSeries.X 1) (F := F) (D := Formalism.L2.Th1.B.FI F i) (c := c)
    (EF := Formalism.L2.Th1.B.fExp (-PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l)))
    (ED := Formalism.L2.Th1.B.fExp (-PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l)))
    (E0 := Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)))
    (E1 := Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l)))
    (P0 := PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) P)
    (P1 := PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 1 l : MvPowerSeries (Fin 2) K) P)
    (ep0 := Formalism.InvariantFactorPaths.G7.at1 0 ep) (ep1 := Formalism.InvariantFactorPaths.G7.at1 1 ep) (c0 := MvPowerSeries.C c0)
    hN (by linear_combination KE) (by linear_combination C0) (by linear_combination C1)
    (by linear_combination hc)
  have hA0 : MvPowerSeries.constantCoeff (PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hF0 _ hψ0
  have hB0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hD0 _ hψ0
  have ha0 : MvPowerSeries.constantCoeff
      (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_inVar 0 hψ0
  have ha1 : MvPowerSeries.constantCoeff
      (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_inVar 1 hψ0
  have m0 := fExp_mul_neg ha0
  have m1 := fExp_mul_neg ha1
  have hc' : -c = Formalism.L2.Th1.B.fExp (-PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l)) *
      Formalism.L2.Th1.B.fExp (-PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l)) *
      Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 *
      Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 := by
    linear_combination
      (-(Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 *
        Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2)) * hEE +
      (c * (Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) *
          Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)) + 1) *
        (Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) *
          Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l))) ^ 2) * m0 +
      (c * (Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) *
          Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l)) + 1)) * m1
  have hprod : Formalism.L2.Th1.B.fExp (-PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l)) *
      Formalism.L2.Th1.B.fExp (-PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l)) *
      Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 *
      Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 =
      Formalism.L2.Th1.B.fExp (-PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l) +
        -PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l) +
        (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)) +
        (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l))) := by
    rw [Formalism.L2.Th1.B.fExp_add, Formalism.L2.Th1.B.fExp_add, Formalism.L2.Th1.B.fExp_add, Formalism.L2.Th1.B.fExp_add, Formalism.L2.Th1.B.fExp_add]
    · ring
    all_goals simp [hA0, hB0, ha0, ha1]
  have hlog : Formalism.L2.Th1.B.fLog (-c) = -PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l) +
        -PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l) +
        (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)) +
        (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l)) := by
    rw [hc', hprod]
    exact Formalism.L2.Th1.B.fLog_fExp (by simp [hA0, hB0, ha0, ha1])
  rw [Formalism.L2.Th1.B.par, hlog]
  ring

end Norm

theorem ParO_of (hA : AddSgStar) (hD : PhODef) (hL : SimeqLog) : ParO := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hCC
  obtain ⟨-, -, h3, c, hcI, hc1, hc⟩ := hCC
  rw [par_eq hA hD hP hF hi h3 hc]
  have h1 : MvPowerSeries.constantCoeff (-c) = 1 := by rw [map_neg, hc1, neg_neg]
  have hI : Formalism.DworkPowerSeriesWeights.Integral (-c) := by
    intro n
    rw [map_neg, norm_neg]
    exact hcI n
  exact (hL K (Fin 2) (-c) h1 hI).2

section Alg2

variable {K : Type} [Field K] [CharZero K]

theorem X_mul_lU {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0) :
    PowerSeries.X * lU l = l := by
  ext n
  cases n with
  | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hl]
  | succ n => rw [PowerSeries.coeff_succ_X_mul, Formalism.L2.Th1.B.lU, PowerSeries.coeff_mk]

theorem constantCoeff_lU (l : PowerSeries K) :
    PowerSeries.constantCoeff (lU l) = PowerSeries.coeff 1 l := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.B.lU, PowerSeries.coeff_mk, zero_add]

theorem psubst_C (l : PowerSeries K) (c : K) :
    PowerSeries.subst l (PowerSeries.C c) = PowerSeries.C c :=
  PowerSeries.subst_C c

theorem diff_eq (hS : Sigma1Sq) {g2 g3 s2 c0 e1 : K} {P l ep : PowerSeries K}
    (hP : IsWp g2 g3 P) (he : 4 * e1 ^ 3 - g2 * e1 - g3 = 0)
    (hl0 : PowerSeries.constantCoeff l = 0) (hl1 : PowerSeries.coeff 1 l = 1)
    (h3 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) :
    2 * (phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l - phO s2 P l) =
      -fLog (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) := by
  have hlS := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hS1 : PowerSeries.constantCoeff
      (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)) = 0 := by
    rw [Formalism.L2.Th1.B.sigmaOneSeries, map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]
  have hS0 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.sigS P) = 0 := by
    rw [Formalism.L2.Th1.B.sigS, map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]
  have hsq := hS K g2 g3 e1 P hP he
  rw [Formalism.L2.Th1.B.sigma1, Formalism.L2.Th1.B.sigma] at hsq
  have hcan : Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)) ^ 2 =
      Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.sigS P) ^ 2 *
        (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (PowerSeries.X_ne_zero (R := K)))
    linear_combination hsq
  have hsub := congrArg (fun φ : PowerSeries K => PowerSeries.subst l φ) hcan
  simp only [PowerSeries.subst_mul hlS, PowerSeries.subst_pow hlS, PowerSeries.subst_sub hlS,
    PowerSeries.subst_add hlS, Formalism.L2.Th1.B.psubst_one hlS, PowerSeries.subst_X hlS, psubst_C l,
    psubst_fExp (u := l) hl0 hS1, psubst_fExp (u := l) hl0 hS0] at hsub
  have hm : PowerSeries.X * Formalism.L2.Th1.B.lU l = l := X_mul_lU hl0
  have h3' : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      PowerSeries.X ^ 2 * (Formalism.L2.Th1.B.lU l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) := by
    linear_combination h3 -
      ((l + PowerSeries.X * Formalism.L2.Th1.B.lU l) * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) * hm
  have hQ := mul_left_cancel₀ (pow_ne_zero 2 (PowerSeries.X_ne_zero (R := K))) h3'
  have eq2 : Formalism.L2.Th1.B.fExp (PowerSeries.subst l
        (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P))) ^ 2 =
      Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) ^ 2 *
        (Formalism.L2.Th1.B.lU l ^ 2 * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) := by
    rw [map_sub]
    linear_combination hsub + (Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) ^ 2) * hQ +
      (Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) ^ 2 * PowerSeries.C e1 *
        (l + PowerSeries.X * Formalism.L2.Th1.B.lU l)) * hm
  have hu : MvPowerSeries.constantCoeff (PowerSeries.subst l
      (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P))) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hl0 _ hS1
  have hv : MvPowerSeries.constantCoeff (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hl0 _ hS0
  have hEu := Formalism.L2.Th1.B.constantCoeff_fExp hu
  have hEv := Formalism.L2.Th1.B.constantCoeff_fExp hv
  have hm1 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l) = 1 := (constantCoeff_lU l).trans hl1
  have hE : MvPowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := by
    have h4 := congrArg (fun φ : PowerSeries K => MvPowerSeries.constantCoeff φ) eq2
    simp only [map_mul, map_pow, hEu, hEv, hm1, one_pow, one_mul] at h4
    exact h4.symm
  have hEvv : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) *
      Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P))) = 1 := by rw [map_mul, hEv, one_mul]
  have hmm : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l * Formalism.L2.Th1.B.lU l) = 1 := by rw [map_mul, hm1, one_mul]
  have hmmE : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l * Formalism.L2.Th1.B.lU l *
      (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) = 1 := by rw [map_mul, hmm, hE, one_mul]
  have key : PowerSeries.subst l (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)) +
        PowerSeries.subst l (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)) =
      PowerSeries.subst l (Formalism.L2.Th1.B.sigS P) + PowerSeries.subst l (Formalism.L2.Th1.B.sigS P) +
        (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU l) + Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU l) +
          Formalism.L2.Th1.B.fLog (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) :=
    calc _ = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.fExp (PowerSeries.subst l
              (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P))) *
            Formalism.L2.Th1.B.fExp (PowerSeries.subst l
              (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)))) := by
          rw [fLog_mul hEu hEu, Formalism.L2.Th1.B.fLog_fExp hu]
      _ = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) *
            Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) *
            (Formalism.L2.Th1.B.lU l * Formalism.L2.Th1.B.lU l * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2))) :=
          congrArg Formalism.L2.Th1.B.fLog (by linear_combination eq2)
      _ = _ := by
          rw [fLog_mul hEvv hmmE, fLog_mul hEv hEv, fLog_mul hmm hE, fLog_mul hm1 hm1,
            Formalism.L2.Th1.B.fLog_fExp hv]
  rw [Formalism.L2.Th1.B.phE, Formalism.L2.Th1.B.phO]
  linear_combination (-1 : PowerSeries K) * key

end Alg2

theorem DiffPh_of (hS : Sigma1Sq) (hL : SimeqLog) : DiffPh := by
  intro K _ _ _ g2 g3 s2 c0 e1 P l i ep F hP he hF hCC
  have key := diff_eq (s2 := s2) hS hP he hF.2.2.1 hF.2.2.2.1 hCC.2.2.1
  refine ⟨key, fun hce => ?_⟩
  have hE1' : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := by
    simp [hCC.2.1]
  have hE1 : MvPowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := hE1'
  have hEI : Formalism.DworkPowerSeriesWeights.Integral (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2 : PowerSeries K) := by
    intro n
    rw [map_add, PowerSeries.C_apply, PowerSeries.X_apply, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_X_pow]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hCC.1 n) ?_)
    split_ifs
    · rw [mul_one]; exact hce
    · rw [mul_zero, norm_zero]; exact zero_le_one
  have hex := (hL K Unit (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) hE1 hEI).2
  have heq : (2 * Formalism.L2.Th1.B.phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P) l -
      2 * Formalism.L2.Th1.B.phO s2 P l : PowerSeries K) =
      -Formalism.L2.Th1.B.fLog (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) - 0 := by
    linear_combination key
  unfold Formalism.InvariantFactorPaths.G7.Simeq at hex ⊢
  rw [heq]
  exact hex

end Formalism.L2.Th1.B.ParO
