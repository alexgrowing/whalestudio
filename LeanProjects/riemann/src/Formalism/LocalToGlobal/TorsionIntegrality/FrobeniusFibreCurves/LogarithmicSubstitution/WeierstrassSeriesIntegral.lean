import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable

noncomputable section

namespace Formalism.L2.Th1.B.ParE

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)

section Alg

variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem hsU {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.HasSubst U :=
  PowerSeries.HasSubst.of_constantCoeff_zero hU

theorem subst_phE (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) {U : MvPowerSeries ι K}
    (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst U (phE s2 e1 kap w l) =
      -PowerSeries.subst (PowerSeries.subst U l) (sigmaOneSeries e1 kap w) +
        MvPowerSeries.C (s2 / 2) * PowerSeries.subst U l ^ 2 := by
  have ha : PowerSeries.HasSubst U := hsU hU
  have hC : PowerSeries.subst U (PowerSeries.C (s2 / 2)) = MvPowerSeries.C (s2 / 2) := by
    have h := (PowerSeries.substAlgHom ha).commutes (s2 / 2)
    rw [PowerSeries.coe_substAlgHom] at h
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply] using h
  unfold phE
  rw [← PowerSeries.coe_substAlgHom ha]
  simp only [map_add, map_neg, map_mul, map_pow]
  rw [PowerSeries.coe_substAlgHom ha, hC,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hl) ha]

theorem subst_inVar (x : ι) (f : PowerSeries K) {l : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) :
    at1 x (PowerSeries.subst l f) = PowerSeries.subst (at1 x l) f := by
  unfold at1
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hl)
    (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X x)) f

theorem subst_parallelogram_defect (f : PowerSeries K) {U V : MvPowerSeries ι K}
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (par0 f) =
      PowerSeries.subst (U + V) f + PowerSeries.subst (U - V) f - 2 * PowerSeries.subst U f -
        2 * PowerSeries.subst V f := by
  have hb : MvPowerSeries.HasSubst ![U, V] :=
    ⟨fun s => by fin_cases s <;> simp [hU, hV, IsNilpotent.zero], fun _ => Set.toFinite _⟩
  have key : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.subst ![U, V] (PowerSeries.subst a f) =
        PowerSeries.subst (MvPowerSeries.subst ![U, V] a) f := fun a ha =>
    MvPowerSeries.subst_comp_subst_apply
      (⟨fun _ => by simp [ha, IsNilpotent.zero], fun _ => Set.toFinite _⟩ :
        MvPowerSeries.HasSubst (fun _ : Unit => a)) hb f
  have hX : ∀ s : Fin 2, MvPowerSeries.subst ![U, V] (MvPowerSeries.X s : MvPowerSeries (Fin 2) K) = ![U, V] s :=
    fun s => MvPowerSeries.subst_X hb s
  unfold par0 atS atD at1
  rw [← MvPowerSeries.coe_substAlgHom hb]
  simp only [map_add, map_sub, map_mul, map_ofNat]
  rw [MvPowerSeries.coe_substAlgHom hb, key _ (by simp), key _ (by simp), key _ (by simp), key _ (by simp),
    ← MvPowerSeries.coe_substAlgHom hb]
  simp only [map_add, map_sub]
  rw [MvPowerSeries.coe_substAlgHom hb, hX 0, hX 1]
  simp

end Alg

private theorem cc_subst_lemma {R : Type*} [CommRing R] {τ : Type*} {a : MvPowerSeries τ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha), map_mul, ha, zero_mul]

private theorem mvSubst_powerSeries_subst_eq_subst_mvSubst {R : Type*} [CommRing R] {σ τ : Type*} {c : σ → MvPowerSeries τ R}
    (hc : MvPowerSeries.HasSubst c) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries R) :
    MvPowerSeries.subst c (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst c a) f :=
  MvPowerSeries.subst_comp_subst_apply
    (⟨fun _ => by simp [ha, IsNilpotent.zero], fun _ => Set.toFinite _⟩ :
      MvPowerSeries.HasSubst (fun _ : Unit => a)) hc f

theorem ParEFormula_of (hA : AddSigma1Log) : ParEFormula := by
  intro K _ _ _ A kap e1 s2 w l i F hW hLL hI
  have hat : ∀ (x : Fin 2) (f : PowerSeries K), at1 x f = PowerSeries.subst (MvPowerSeries.X x) f :=
    fun _ _ => rfl
  have hl0 : PowerSeries.constantCoeff l = 0 := hLL.2.2.1
  have hx0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (at1 x l) = 0 := fun x => by
    rw [hat]
    exact cc_subst_lemma (MvPowerSeries.constantCoeff_X x) hl0
  have L1 : PowerSeries.subst F l = at1 (0 : Fin 2) l + at1 (1 : Fin 2) l := by
    have h := hLL.2.2.2.2
    unfold cob at h
    linear_combination h
  have L2 : PowerSeries.subst (FI F i) l = at1 (0 : Fin 2) l - at1 (1 : Fin 2) l := by
    have hci : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0 := by
      rw [hat]
      exact cc_subst_lemma (MvPowerSeries.constantCoeff_X 1) hI.1
    have hc : MvPowerSeries.HasSubst ![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K), at1 (1 : Fin 2) i] :=
      ⟨fun s => by fin_cases s <;> simp [hci, IsNilpotent.zero], fun _ => Set.toFinite _⟩
    have hneg : at1 (1 : Fin 2) (-l) = -at1 (1 : Fin 2) l := by
      rw [hat, hat, ← PowerSeries.coe_substAlgHom
        (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X (1 : Fin 2))), map_neg]
    unfold FI
    rw [← mvSubst_powerSeries_subst_eq_subst_mvSubst hc hLL.1 l, L1, ← MvPowerSeries.coe_substAlgHom hc, map_add,
      MvPowerSeries.coe_substAlgHom hc, hat 0 l, hat 1 l,
      mvSubst_powerSeries_subst_eq_subst_mvSubst hc (MvPowerSeries.constantCoeff_X 0) l, mvSubst_powerSeries_subst_eq_subst_mvSubst hc (MvPowerSeries.constantCoeff_X 1) l,
      MvPowerSeries.subst_X hc, MvPowerSeries.subst_X hc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← subst_inVar (1 : Fin 2) l hI.1, hI.2.2, hneg, hat 1 l]
    ring
  have hP : PowerSeries.subst (at1 (0 : Fin 2) l + at1 (1 : Fin 2) l) (sigmaOneSeries e1 kap w) +
      PowerSeries.subst (at1 (0 : Fin 2) l - at1 (1 : Fin 2) l) (sigmaOneSeries e1 kap w) -
      2 * PowerSeries.subst (at1 (0 : Fin 2) l) (sigmaOneSeries e1 kap w) - 2 * PowerSeries.subst (at1 (1 : Fin 2) l) (sigmaOneSeries e1 kap w) =
      MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] (fLog (1 - MvPowerSeries.C kap * at1 (0 : Fin 2) w * at1 (1 : Fin 2) w)) := by
    rw [← hA K A kap e1 w hW, subst_parallelogram_defect _ (hx0 0) (hx0 1)]
  have hFL : MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] (fLog (1 - MvPowerSeries.C kap * at1 (0 : Fin 2) w * at1 (1 : Fin 2) w)) =
      fLog (1 - MvPowerSeries.C kap * at1 (0 : Fin 2) (PowerSeries.subst l w) * at1 (1 : Fin 2) (PowerSeries.subst l w)) := by
    have hab : MvPowerSeries.HasSubst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] :=
      ⟨fun s => by fin_cases s <;> simp [hx0, IsNilpotent.zero], fun _ => Set.toFinite _⟩
    have hw0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (at1 x w) = 0 := fun x => by
      rw [hat]
      exact cc_subst_lemma (MvPowerSeries.constantCoeff_X x) hW.1
    have hg : MvPowerSeries.constantCoeff
        ((1 : MvPowerSeries (Fin 2) K) - MvPowerSeries.C kap * at1 (0 : Fin 2) w * at1 (1 : Fin 2) w - 1) = 0 := by
      rw [map_sub, map_sub, map_one, map_mul, map_mul, hw0 0, hw0 1]
      simp
    have hCk : MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] (MvPowerSeries.C kap : MvPowerSeries (Fin 2) K) =
        MvPowerSeries.C kap := by
      have h := (MvPowerSeries.substAlgHom hab).commutes kap
      rw [MvPowerSeries.coe_substAlgHom] at h
      simpa [MvPowerSeries.algebraMap_apply] using h
    have hw : ∀ x : Fin 2, MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] (at1 x w) = at1 x (PowerSeries.subst l w) := by
      intro x
      rw [hat x w, mvSubst_powerSeries_subst_eq_subst_mvSubst hab (MvPowerSeries.constantCoeff_X x) w, MvPowerSeries.subst_X hab,
        subst_inVar x w hl0]
      fin_cases x <;> simp
    unfold fLog
    rw [mvSubst_powerSeries_subst_eq_subst_mvSubst hab hg, ← MvPowerSeries.coe_substAlgHom hab]
    simp only [map_sub, map_one, map_mul]
    rw [MvPowerSeries.coe_substAlgHom hab, hCk, hw 0, hw 1]
  unfold par
  rw [subst_phE s2 e1 kap w hl0 hLL.1, L1, subst_phE s2 e1 kap w hl0 (law_constantCoeff_FI hLL hI), L2,
    hat 0 (phE s2 e1 kap w l), hat 1 (phE s2 e1 kap w l),
    subst_phE s2 e1 kap w hl0 (MvPowerSeries.constantCoeff_X (0 : Fin 2)),
    subst_phE s2 e1 kap w hl0 (MvPowerSeries.constantCoeff_X (1 : Fin 2)), ← hat 0 l, ← hat 1 l]
  linear_combination -hP - hFL

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type}

theorem integral_sub' {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f - g) := by
  intro n
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) ?_)
  rw [norm_neg]
  exact hg n

theorem integral_add' {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f + g) := by
  intro n
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem integral_C' {c : K} (hc : ‖c‖ ≤ 1) : Integral (MvPowerSeries.C c : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · simp

end Norm

theorem ParE_of (hF : ParEFormula) (hL : SimeqLog) : ParE := by
  intro K _ _ _ A kap e1 s2 w l i F hW hLL hI hk hInt
  rw [hF K A kap e1 s2 w l i F hW hLL hI]
  refine (hL K (Fin 2) _ ?_ ?_).2
  · have hs : MvPowerSeries.constantCoeff (PowerSeries.subst l w) = 0 :=
      cc_subst_lemma hLL.2.2.1 hW.1
    have h0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (at1 x (PowerSeries.subst l w)) = 0 := by
      intro x
      unfold at1
      exact cc_subst_lemma (MvPowerSeries.constantCoeff_X x) hs
    rw [map_sub, map_one, map_mul, map_mul, h0 0, h0 1]
    simp
  · exact integral_sub' integral_one' (integral_mul' (integral_mul' (integral_C' hk)
      (integral_series_at_variable 0 _ hInt)) (integral_series_at_variable 1 _ hInt))

theorem weierstrass_series_integral : WIntegral := by
  intro K _ _ _ c0 e1 P l i ep F hLL hCH hce
  obtain ⟨hepI, hep1, hcurve, -⟩ := hCH
  have hl0 : PowerSeries.constantCoeff l = 0 := hLL.2.2.1
  have hl1 : PowerSeries.coeff 1 l = 1 := hLL.2.2.2.1
  have ha : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero hl0
  have hlne : l ≠ 0 := by
    rintro rfl
    simp at hl1
  have hD0c : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2 : PowerSeries K) ≠ 0 := by
    simp
  have hCe : PowerSeries.subst l (PowerSeries.C e1 : PowerSeries K) = (PowerSeries.C e1 : PowerSeries K) := by
    have h := (PowerSeries.substAlgHom ha).commutes e1
    rw [PowerSeries.coe_substAlgHom] at h
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply] using h
  have hw : wOf e1 P * (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) =
      PowerSeries.X ^ 2 := by
    unfold wOf
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD0c, mul_one]
  have hWD : PowerSeries.subst l (wOf e1 P) *
      (1 + l ^ 2 * PowerSeries.subst l P - PowerSeries.C e1 * l ^ 2) = l ^ 2 := by
    have h := congrArg (PowerSeries.subst l) hw
    rw [← PowerSeries.coe_substAlgHom ha] at h
    simp only [map_add, map_sub, map_one, map_mul, map_pow] at h
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_X ha, hCe] at h
    exact h
  have hkey : PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) * l ^ 2 =
      PowerSeries.X ^ 2 * l ^ 2 := by
    rw [map_sub]
    linear_combination (-PowerSeries.subst l (wOf e1 P)) * hcurve + PowerSeries.X ^ 2 * hWD
  have h1 : PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) =
      PowerSeries.X ^ 2 := mul_right_cancel₀ (pow_ne_zero 2 hlne) hkey
  refine ⟨h1, ?_⟩
  have hX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := law_integral_X ()
  have hX2 : Integral (ι := Unit) (PowerSeries.X ^ 2 : PowerSeries K) := by
    rw [pow_two]
    exact integral_mul' hX hX
  have hEI : Integral (ι := Unit) (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) :=
    integral_add' hepI (integral_mul' (integral_C' hce) hX2)
  have hEc : MvPowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2 : PowerSeries K) = 1 := by
    have h : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := by
      simp [hep1]
    exact h
  have hEc' : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) ≠ 0 := by
    simp [hep1]
  have hVI : Integral (ι := Unit) (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ :=
    integral_of_mul_eq_one hEI hEc (PowerSeries.inv_mul_cancel _ hEc')
  have hWe : PowerSeries.subst l (wOf e1 P) =
      PowerSeries.X ^ 2 * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ := by
    calc PowerSeries.subst l (wOf e1 P)
        = PowerSeries.subst l (wOf e1 P) * ((ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) *
            (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹) := by
          rw [PowerSeries.mul_inv_cancel _ hEc', mul_one]
      _ = (PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) *
            (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ := by
          rw [mul_assoc]
      _ = _ := by rw [h1]
  rw [hWe]
  exact integral_mul' hX2 hVI

end Formalism.L2.Th1.B.ParE
