import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.EndInt
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeW
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds

open PowerSeries

noncomputable section

namespace Formalism.L2.KerInert.PN

open Formalism.L2.KerInert.VC

section Field

variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)

theorem g_change' : Formalism.L2.Th1.A.g₂ (C • W) = ((C.u⁻¹ : Kˣ) : K) ^ 4 * Formalism.L2.Th1.A.g₂ W ∧
    Formalism.L2.Th1.A.g₃ (C • W) = ((C.u⁻¹ : Kˣ) : K) ^ 6 * Formalism.L2.Th1.A.g₃ W := by
  refine ⟨?_, ?_⟩
  · simp only [Formalism.L2.Th1.A.g₂, WeierstrassCurve.variableChange_c₄]
    ring
  · simp only [Formalism.L2.Th1.A.g₃, WeierstrassCurve.variableChange_c₆]
    ring

theorem wpReg_change : Formalism.L2.Th1.A.wpReg (C • W) =
    PowerSeries.C (((C.u⁻¹ : Kˣ) : K) ^ 2) * PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.A.wpReg W) := by
  rw [Formalism.L2.KerInert.Sigma.wpReg_eq, Formalism.L2.KerInert.Sigma.wpReg_eq, (g_change' W C).1, (g_change' W C).2]
  exact (Formalism.L2.Th1.F.seriesScale K _ _ _).2.2.2.1

private lemma prim_rescale (a : K) (ha : a ≠ 0) (f : K⟦X⟧) :
    Formalism.L2.Th1.B.prim (PowerSeries.rescale a f) =
      PowerSeries.C a⁻¹ * PowerSeries.rescale a (Formalism.L2.Th1.B.prim f) := by
  ext n
  rcases n with _ | m
  · simp [Formalism.L2.Th1.B.prim]
  · simp only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [pow_succ]
    field_simp

private lemma prim_C_mul' (c : K) (f : K⟦X⟧) :
    Formalism.L2.Th1.B.prim (PowerSeries.C c * f) = PowerSeries.C c * Formalism.L2.Th1.B.prim f := by
  ext n
  rcases n with _ | m
  · simp [Formalism.L2.Th1.B.prim]
  · simp only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Nat.succ_ne_zero,
      if_false]
    ring

private lemma fExp_rescale (a : K) (f : K⟦X⟧) (hf : PowerSeries.constantCoeff f = 0) :
    Formalism.L2.Th1.B.fExp (PowerSeries.rescale a f) = PowerSeries.rescale a (Formalism.L2.Th1.B.fExp f) := by
  unfold Formalism.L2.Th1.B.fExp
  have hf' := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  have hX : PowerSeries.HasSubst ((a • PowerSeries.X : K⟦X⟧)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  rw [PowerSeries.rescale_eq_subst a (PowerSeries.subst f (PowerSeries.exp K)),
    PowerSeries.subst_comp_subst_apply hf' hX, ← PowerSeries.rescale_eq_subst]

theorem sgW_change (s2 : K) : Formalism.L2.Th1.B.sgW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2) =
    PowerSeries.C ((C.u : Kˣ) : K) * PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.B.sgW W s2) := by
  have hl : ((C.u⁻¹ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hul : ((C.u : Kˣ) : K) * ((C.u⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRC : ∀ c : K, PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (PowerSeries.C c) = PowerSeries.C c := by
    intro c
    ext n
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
    split_ifs with h <;> simp [h]
  unfold Formalism.L2.Th1.B.sgW Formalism.L2.Th1.B.sgStar Formalism.L2.Th1.B.sigma Formalism.L2.Th1.B.sigS
  rw [wpReg_change W C]
  have hpp : Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (PowerSeries.C (((C.u⁻¹ : Kˣ) : K) ^ 2) *
      PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.A.wpReg W))) =
      PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K)
        (Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (Formalism.L2.Th1.A.wpReg W))) := by
    rw [prim_C_mul', prim_rescale _ hl, ← mul_assoc, ← map_mul, prim_C_mul',
      prim_rescale _ hl, ← mul_assoc, ← map_mul]
    have h1 : ((C.u⁻¹ : Kˣ) : K) ^ 2 * ((C.u⁻¹ : Kˣ) : K)⁻¹ * ((C.u⁻¹ : Kˣ) : K)⁻¹ = 1 := by
      field_simp
    rw [h1, map_one, one_mul]
  have hT : -(PowerSeries.C (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2 / 2) * PowerSeries.X ^ 2 : K⟦X⟧) =
      PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) := by
    rw [map_neg, map_mul, map_pow, PowerSeries.rescale_X, hRC, mul_pow, ← map_pow, ← mul_assoc,
      ← map_mul, show ((C.u⁻¹ : Kˣ) : K) ^ 2 * s2 / 2 = s2 / 2 * ((C.u⁻¹ : Kˣ) : K) ^ 2 by ring]
  have hS0 : PowerSeries.constantCoeff (-Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (Formalism.L2.Th1.A.wpReg W))) = 0 := by
    rw [map_neg, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [Formalism.L2.Th1.B.prim]
  have hT0 : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2 : K⟦X⟧)) = 0 := by
    simp
  rw [hpp, hT, ← map_neg, fExp_rescale _ _ hS0, fExp_rescale _ _ hT0, map_mul, map_mul,
    PowerSeries.rescale_X]
  simp only [← mul_assoc, ← map_mul, hul, map_one, one_mul]

theorem subst_rescale' (a : K) (f : PowerSeries K) {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.subst g (PowerSeries.rescale a f) = PowerSeries.subst (PowerSeries.C a * g) f := by
  have hg' := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have hX : PowerSeries.HasSubst ((a • PowerSeries.X : K⟦X⟧)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hX hg']
  congr 1
  rw [← PowerSeries.coe_substAlgHom hg', map_smul, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hg', PowerSeries.smul_eq_C_mul]

theorem subst_neg' {f a : K⟦X⟧} (ha : constantCoeff a = 0) : (-f).subst a = -(f.subst a) := by
  have h := HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coe_substAlgHom h, map_neg]

theorem subst_sub' {f g a : K⟦X⟧} (ha : constantCoeff a = 0) : (f - g).subst a = f.subst a - g.subst a := by
  have h := HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coe_substAlgHom h, map_sub]

theorem subst_smul' {f a : K⟦X⟧} (ha : constantCoeff a = 0) (c : K) : (c • f).subst a = c • (f.subst a) := by
  have h := HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coe_substAlgHom h, map_smul]

private lemma subst_fExp' {a f : K⟦X⟧} (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst a (Formalism.L2.Th1.B.fExp f) = Formalism.L2.Th1.B.fExp (PowerSeries.subst a f) :=
  (Formalism.L2.Th1.B.expLogSubst K Unit Unit (fun _ => a) (fun _ => ha)).1 f hf

theorem exp_rel (s2 : K) :
    phi W C * Formalism.L2.Th1.B.fExp (-((Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)).subst (phi W C))) =
      PowerSeries.C ((C.u : Kˣ) : K) * (X * Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.phW W s2))) := by
  have hφ0 : PowerSeries.constantCoeff (phi W C) = 0 := by
    rw [Formalism.L2.KerInert.VC.phi_eq]; simp
  have hφ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0
  have hℓ0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer W) = 0 := Formalism.L2.Th1.A.ZSer.log_cc (W := W)
  have hℓ0' : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer (C • W)) = 0 :=
    Formalism.L2.Th1.A.ZSer.log_cc (W := C • W)
  have hℓ' := PowerSeries.HasSubst.of_constantCoeff_zero' hℓ0'
  have hcs := Formalism.L2.Th1.B.curveSigma K W s2
  have hcs' := Formalism.L2.Th1.B.curveSigma K (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)
  have hnP0 : PowerSeries.constantCoeff
      (-Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) = 0 := by
    rw [map_neg, hcs'.1, neg_zero]
  have hul : ((C.u⁻¹ : Kˣ) : K) * ((C.u : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcu0 : PowerSeries.constantCoeff (PowerSeries.C ((C.u : Kˣ) : K) * Formalism.L2.Th1.A.logSer W) = 0 := by
    simp [hℓ0]
  have step1 : phi W C * Formalism.L2.Th1.B.fExp
      (-((Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)).subst (phi W C))) =
      PowerSeries.subst (phi W C)
        (X * Formalism.L2.Th1.B.fExp (-Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2))) := by
    rw [← PowerSeries.coe_substAlgHom hφ, map_mul, PowerSeries.coe_substAlgHom hφ,
      PowerSeries.subst_X hφ, subst_fExp' hφ0 hnP0, subst_neg' hφ0]
  have hsm : PowerSeries.C ((C.u : Kˣ) : K) *
      PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.B.sgW W s2) =
      ((C.u : Kˣ) : K) • PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.B.sgW W s2) :=
    (PowerSeries.smul_eq_C_mul _ _).symm
  rw [step1, ← hcs'.2.1, PowerSeries.subst_comp_subst_apply hℓ' hφ, Formalism.L2.KerInert.VC.log_phi,
    sgW_change, hsm, subst_smul' hcu0, subst_rescale' _ _ hcu0,
    ← mul_assoc (PowerSeries.C _) (PowerSeries.C _) (Formalism.L2.Th1.A.logSer W), ← map_mul PowerSeries.C,
    hul, map_one, one_mul, hcs.2.1]
  exact PowerSeries.smul_eq_C_mul _ _

end Field

section Cong

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts

variable {K : Type} [Field K] [CharZero K] {R' : Subring K}

theorem lg_intsmul (N : ℤ) {f : K⟦X⟧} (hf : LG R' (f : MvPowerSeries Unit K)) :
    LG R' (((N : K) • f : K⟦X⟧) : MvPowerSeries Unit K) := by
  obtain ⟨h0, hadd, hneg⟩ := Formalism.L2.Th1.C.lGSubgroup K R' Unit
  have key : ∀ n : ℕ, LG R' ((((n : ℤ) : K) • f : K⟦X⟧) : MvPowerSeries Unit K) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have h1 := hadd _ _ ih hf
      have e : ((((n + 1 : ℕ) : ℤ) : K) • f : K⟦X⟧) = (((n : ℤ) : K) • f : K⟦X⟧) + f := by
        push_cast
        rw [add_smul, one_smul]
      rw [e]
      exact h1
  rcases Int.eq_nat_or_neg N with ⟨n, rfl | rfl⟩
  · exact key n
  · have h1 := hneg _ (key n)
    have e : (((-(n : ℤ) : ℤ) : K) • f : K⟦X⟧) = -((((n : ℤ) : K) • f : K⟦X⟧)) := by
      push_cast
      rw [neg_smul]
    rw [e]
    exact h1

theorem integral_phi1_variable_change (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R') :
    IntPS R' (PowerSeries.C ((C.u : Kˣ) : K) * (1 - PowerSeries.C C.r * X ^ 2 * Formalism.L2.Th1.A.wU W) * vv W C) := by
  have h := Formalism.L2.KerInert.VC.intPS_phi W hW C hu hr hs ht
  rw [Formalism.L2.KerInert.VC.phi_eq] at h
  intro n
  have h1 := h (n + 1)
  rwa [PowerSeries.coeff_succ_X_mul] at h1

theorem cong_phi (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hu' : ((C.u⁻¹ : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R')
    (s2 : K) :
    Cong R' ((PowerSeries.subst (phi W C) (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) : K⟦X⟧) :
      MvPowerSeries Unit K) ((Formalism.L2.Th1.B.phW W s2 : K⟦X⟧) : MvPowerSeries Unit K) := by
  have hφ0 : PowerSeries.constantCoeff (phi W C) = 0 := by
    rw [Formalism.L2.KerInert.VC.phi_eq]; simp
  have hφ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0
  have hcs := Formalism.L2.Th1.B.curveSigma K W s2
  have hcs' := Formalism.L2.Th1.B.curveSigma K (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)
  have key := exp_rel W C s2
  obtain ⟨A, hA⟩ : ∃ A : K⟦X⟧, A = PowerSeries.subst (phi W C)
      (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : K⟦X⟧, B = Formalism.L2.Th1.B.phW W s2 := ⟨_, rfl⟩
  rw [← hA, ← hB]
  rw [← hA, ← hB] at key
  obtain ⟨Q, hQ⟩ := PowerSeries.X_dvd_iff.mpr hcs'.1
  have hA0 : PowerSeries.constantCoeff A = 0 := by
    rw [hA, hQ, ← PowerSeries.coe_substAlgHom hφ, map_mul, PowerSeries.coe_substAlgHom hφ,
      PowerSeries.subst_X hφ, map_mul, hφ0, zero_mul]
  have hB0 : PowerSeries.constantCoeff B = 0 := by rw [hB]; exact hcs.1
  have hnA0 : PowerSeries.constantCoeff (-A) = 0 := by rw [map_neg, hA0, neg_zero]
  have hnB0 : PowerSeries.constantCoeff (-B) = 0 := by rw [map_neg, hB0, neg_zero]
  have hER := Formalism.L2.Th1.B.expLogRules K Unit
  have hfe0 : Formalism.L2.Th1.B.fExp (0 : K⟦X⟧) = 1 := by
    have h1 := hER.1 (0 : K⟦X⟧) 0 (map_zero _) (map_zero _)
    rw [add_zero] at h1
    have hu0 : IsUnit (Formalism.L2.Th1.B.fExp (0 : K⟦X⟧)) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, (hER.2.1 0 (map_zero _)).1]
      exact isUnit_one
    exact hu0.mul_left_cancel (by rw [mul_one]; exact h1.symm)
  have hAA : Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-A) = 1 := by
    rw [← hER.1 A (-A) hA0 hnA0, add_neg_cancel, hfe0]
  have hAB : Formalism.L2.Th1.B.fExp (A - B) = Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-B) := by
    rw [sub_eq_add_neg, hER.1 A (-B) hA0 hnB0]
  obtain ⟨V, hV⟩ : ∃ V : K⟦X⟧, V = PowerSeries.C ((C.u : Kˣ) : K) *
      (1 - PowerSeries.C C.r * X ^ 2 * Formalism.L2.Th1.A.wU W) * vv W C := ⟨_, rfl⟩
  have hφV : phi W C = X * V := by rw [Formalism.L2.KerInert.VC.phi_eq, hV]
  rw [hφV] at key
  have key2 : V * Formalism.L2.Th1.B.fExp (-A) = PowerSeries.C ((C.u : Kˣ) : K) * Formalism.L2.Th1.B.fExp (-B) := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := K))
    rw [← mul_assoc, key]
    ring
  have hul : ((C.u⁻¹ : Kˣ) : K) * ((C.u : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hE : Formalism.L2.Th1.B.fExp (A - B) = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V := by
    rw [hAB]
    calc Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-B)
        = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * (PowerSeries.C ((C.u : Kˣ) : K) * Formalism.L2.Th1.B.fExp (-B)) *
          Formalism.L2.Th1.B.fExp A := by
          rw [← mul_assoc, ← map_mul, hul, map_one, one_mul, mul_comm]
      _ = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * (V * Formalism.L2.Th1.B.fExp (-A)) * Formalism.L2.Th1.B.fExp A := by
          rw [key2]
      _ = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V * (Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-A)) := by
          ring
      _ = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V := by rw [hAA, mul_one]
  have hVi : Formalism.L2.Th1.C.IntPS R' V := by rw [hV]; exact integral_phi1_variable_change W hW C hu hr hs ht
  show Formalism.L2.Th1.C.LG R' ((A : MvPowerSeries Unit K) - B)
  refine ⟨?_, ?_⟩
  · show PowerSeries.constantCoeff (A - B) = 0
    rw [map_sub, hA0, hB0, sub_zero]
  · show Formalism.L2.Th1.C.IntMv R' (Formalism.L2.Th1.B.fExp (A - B))
    rw [hE]
    intro n
    rw [Finsupp.unique_single n]
    show PowerSeries.coeff (n default) (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V) ∈ R'
    rw [PowerSeries.coeff_C_mul]
    exact R'.mul_mem hu' (hVi (n default))

end Cong

section Transfer

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc

variable {K : Type} [Field K] [CharZero K] {R' : Subring K}

private lemma powerSeries_subst_X (f : K⟦X⟧) : PowerSeries.subst (X : K⟦X⟧) f = f := by
  rw [← one_smul K (X : K⟦X⟧), ← PowerSeries.rescale_eq_subst, PowerSeries.rescale_one, RingHom.id_apply]

private lemma intMv_coe_of_intPS {f : K⟦X⟧} (h : IntPS R' f) : IntMv R' (f : MvPowerSeries Unit K) := by
  intro n
  rw [Finsupp.unique_single n]
  exact h (n default)

private lemma constantCoeff_compInv (f : K⟦X⟧) : PowerSeries.constantCoeff (Formalism.L2.Th1.A.compInv f) = 0 := by
  unfold Formalism.L2.Th1.A.compInv
  split_ifs with h
  · exact h.choose_spec.1
  · simp

private lemma constantCoeff_subst_eq_zero_inert_coprime {a f : K⟦X⟧} (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) : PowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨Q, hQ⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [hQ, ← PowerSeries.coe_substAlgHom hs, map_mul, PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs,
    map_mul, ha, zero_mul]

theorem phNormAt_varChange (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hu' : ((C.u⁻¹ : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R')
    (s2 c cb : K) (N : ℤ) (hN : c * cb = N)
    (hE : EndInt R' (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c)
    (h : PhNormAt R' (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) (Formalism.L2.Th1.B.phW W s2) c cb) :
    PhNormAt R' (Formalism.L2.Th1.A.logSer (C • W)) (Formalism.L2.Th1.A.expSer (C • W))
      (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) c cb := by
  have hφ0 : PowerSeries.constantCoeff (phi W C) = 0 := by
    rw [Formalism.L2.KerInert.VC.phi_eq]; simp
  have hφ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0
  have h1 : PowerSeries.coeff 1 (phi W C) = ((C.u : Kˣ) : K) := by
    rw [Formalism.L2.KerInert.VC.phi_eq, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [Formalism.L2.KerInert.VC.vv, PowerSeries.constantCoeff_invOfUnit]
  have huu : ((C.u : Kˣ) : K) * ((C.u⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have spec := Formalism.L2.Th1.A.compInvSpec K (phi W C) hφ0 (by rw [h1]; exact (C.u).isUnit)
  have hψ0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.compInv (phi W C)) = 0 := spec.1
  have hψ := PowerSeries.HasSubst.of_constantCoeff_zero' hψ0
  have hψI : IntPS R' (Formalism.L2.Th1.A.compInv (phi W C)) :=
    Formalism.L2.KerInert.VC.intPS_compInv (R' := R') (hf := Formalism.L2.KerInert.VC.intPS_phi W hW C hu hr hs ht)
      (h0 := hφ0) (hui := hu') (h1 := h1) (huu := huu)
  have hψpt : IsPt R' ((Formalism.L2.Th1.A.compInv (phi W C) : K⟦X⟧) : MvPowerSeries Unit K) := ⟨hψ0, intMv_coe_of_intPS hψI⟩
  have hℓ0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer W) = 0 := Formalism.L2.Th1.A.ZSer.log_cc (W := W)
  have hm0 : PowerSeries.constantCoeff (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) = 0 := by
    unfold mulBy
    exact constantCoeff_subst_eq_zero_inert_coprime (by simp [hℓ0]) (constantCoeff_compInv _)
  have hm := PowerSeries.HasSubst.of_constantCoeff_zero' hm0
  have hmψ0 : PowerSeries.constantCoeff (PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C))
      (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c)) = 0 := constantCoeff_subst_eq_zero_inert_coprime hψ0 hm0
  have hmψ := PowerSeries.HasSubst.of_constantCoeff_zero' hmψ0
  have hmψpt : IsPt R' ((PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C))
      (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) : K⟦X⟧) : MvPowerSeries Unit K) :=
    ⟨hmψ0, Formalism.L2.Th1.C.intSubst K R' _ hE Unit _ hψpt⟩
  have hD := cong_phi W hW C hu hu' hr hs ht s2
  obtain ⟨D, hDdef⟩ : ∃ D : K⟦X⟧, D = PowerSeries.subst (phi W C)
      (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) - Formalism.L2.Th1.B.phW W s2 := ⟨_, rfl⟩
  have hDLG : LG R' (D : MvPowerSeries Unit K) := by rw [hDdef]; exact hD
  have e1 : PowerSeries.subst (phi W C) (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) =
      Formalism.L2.Th1.B.phW W s2 + D := by rw [hDdef]; ring
  have e2 : Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2) =
      PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C)) (Formalism.L2.Th1.B.phW W s2 + D) := by
    rw [← e1, PowerSeries.subst_comp_subst_apply hφ hψ, spec.2.1, powerSeries_subst_X]
  have hadd : ∀ (a f g : K⟦X⟧), PowerSeries.HasSubst a →
      PowerSeries.subst a (f + g) = PowerSeries.subst a f + PowerSeries.subst a g := by
    intro a f g ha
    rw [← PowerSeries.coe_substAlgHom ha, map_add]
  have hL1 := Formalism.L2.Th1.C.lGSubst K R' _ h Unit _ hψpt
  have hL2 := Formalism.L2.Th1.C.lGSubst K R' _ hDLG Unit _ hmψpt
  have hL3 := lg_intsmul N (Formalism.L2.Th1.C.lGSubst K R' _ hDLG Unit _ hψpt)
  unfold PhNormAt Cong
  rw [Formalism.L2.KerInert.VC.mulBy_eq, ← PowerSeries.subst_comp_subst_apply hφ hmψ, e1, hadd _ _ _ hmψ,
    ← PowerSeries.subst_comp_subst_apply hm hψ]
  rw [e2]
  rw [hadd _ _ _ hψ, hN]
  have e3 : PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C))
      (PowerSeries.subst (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) (Formalism.L2.Th1.B.phW W s2)
        - (N : K) • Formalism.L2.Th1.B.phW W s2) =
      PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C))
        (PowerSeries.subst (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) (Formalism.L2.Th1.B.phW W s2))
      - (N : K) • PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C)) (Formalism.L2.Th1.B.phW W s2) := by
    rw [subst_sub' hψ0, subst_smul' hψ0]
  rw [hN] at hL1
  rw [e3] at hL1
  have := Formalism.L2.Th1.C.Calc.lg_add (Formalism.L2.Th1.C.Calc.lg_add hL1 hL2) (Formalism.L2.Th1.C.Calc.lg_neg hL3)
  convert this using 1
  rw [smul_add]
  abel

end Transfer

section Main

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField Formalism.L2.KerInert.IwahoriBlocks

theorem phNormOKInert_of : Formalism.L2.KerInert.PhNormOKInert := by
  intro D p _ cc δ g hAt h5 hIn hOW a _hcop
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := hAt
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12
  obtain ⟨⟨L, hL⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := Formalism.L2.KerInert.Sigma.invAlg' D cc δ hcurve hδ12 L hL
  have hs2 := Formalism.L2.KerInert.Sigma.secondEisensteinAlgebraic D cc δ hcurve hδ12 L hL
  set a2 : Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Qbar := ⟨L.g₃, hg3⟩ with ha3
  set s0 : Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs2⟩ with hs0
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hcmby := Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.hasCMBy_curve D cc δ hcurve hδ12 L hL
  have hdisc := Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.disc_curve D cc δ hcurve hδ12 L hL
  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p g.lam
  have hιg2 : ι L.g₂ = g.lam a2 := hι a2
  have hιg3 : ι L.g₃ = g.lam a3 := hι a3
  have hιs : ι (Formalism.L2.Th1.F.s2 L) = g.lam s0 := hι s0
  have hwm : wModel g.lam g.abelian₂ = Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) := by
    have e4 : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam a2) / 4 := by
      have : -(g2 g.abelian₂) / 4 = ((-a2 / 4 : Qbar) : ℂ) := by rw [e2]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    have e6 : lamC g.lam (-(g3 g.abelian₂) / 4) = -(g.lam a3) / 4 := by
      have : -(g3 g.abelian₂) / 4 = ((-a3 / 4 : Qbar) : ℂ) := by rw [e3]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    rw [hιg2, hιg3]
    ext <;> simp [wModel, Formalism.L2.Th1.A.shortW, e4, e6]
  set W0 : WeierstrassCurve ℂ_[p] := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) with hW0
  have hgW : g.W = g.C • W0 := by rw [G1.W, hwm]
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε

  have hΔ0 : W0.Δ = 1 := by
    have e : W0.Δ = ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 := by
      simp only [hW0, Formalism.L2.Th1.A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [e, ← map_pow, ← map_pow, ← map_ofNat ι 27, ← map_mul, ← map_sub, hdisc, map_one]
  obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
  obtain ⟨w1, w2, w3, w4, w6⟩ := hOW
  obtain ⟨k2, k3, n2, n3, nd⟩ := Formalism.L2.KerInert.Sigma.inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
  have j1 : ‖(g.C • W0).a₁‖ ≤ 1 := by rw [← hgW]; exact i1
  have j2 : ‖(g.C • W0).a₂‖ ≤ 1 := by rw [← hgW]; exact i2
  have j3 : ‖(g.C • W0).a₃‖ ≤ 1 := by rw [← hgW]; exact i3
  have jΔ : ‖(g.C • W0).Δ‖ = 1 := by rw [← hgW]; exact hΔ
  obtain ⟨hu, hui, hr, hs, ht⟩ := vc_params h5 W0 rfl rfl rfl (by rw [hΔ0, norm_one]) g.C j1 j2 j3 jΔ
  have hW0' := Formalism.L2.KerInert.Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  rw [hwm] at hW0'
  obtain ⟨c2, c3⟩ := g_change' W0 g.C
  rw [← hgW, hW0'.1] at c2
  rw [← hgW, hW0'.2] at c3
  obtain ⟨t2, -⟩ := norm_two_three (p := p) h5
  have t4 : ‖(4 : ℂ_[p])‖ = 1 := by
    rw [show (4 : ℂ_[p]) = 2 * 2 by norm_num, norm_mul, t2, one_mul]
  have m2 : ‖ι L.g₂‖ ≤ 1 := by
    rw [c2, norm_mul, norm_pow, hui, one_pow, one_mul, ← hιg2] at n2; exact n2
  have m3 : ‖ι L.g₃‖ ≤ 1 := by
    rw [c3, norm_mul, norm_pow, hui, one_pow, one_mul, ← hιg3] at n3; exact n3
  have hIC : Formalism.L2.Th1.E.IntCurve (Formalism.L2.Th1.E.curveL p L ι) := by
    refine ⟨by simp [Formalism.L2.Th1.E.curveL, Formalism.L2.Th1.A.shortW], by simp [Formalism.L2.Th1.E.curveL, Formalism.L2.Th1.A.shortW],
      by simp [Formalism.L2.Th1.E.curveL, Formalism.L2.Th1.A.shortW], ?_, ?_, ?_⟩
    · show ‖-(ι L.g₂) / 4‖ ≤ 1
      rw [norm_div, norm_neg, t4, div_one]; exact m2
    · show ‖-(ι L.g₃) / 4‖ ≤ 1
      rw [norm_div, norm_neg, t4, div_one]; exact m3
    · show ‖W0.Δ‖ = 1
      rw [hΔ0, norm_one]
  have hcoef0 : Formalism.L2.Th1.C.CoeffIn (RB p) W0 := by
    obtain ⟨q1, q2, q3, q4, q6, -⟩ := hIC
    exact ⟨q1, q2, q3, q4, q6⟩

  obtain ⟨ωK, hω, hspan⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.covA_span D.host.K D.host.d (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discriminant_mod_four D)
    ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_sq D)
    (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_finrank_K D)
  set xs : D.host.K := ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ with hxs
  have hx2 : (D.host.φ₀ (xs : D.host.E)) ^ 2 = -(D.host.d : ℂ) := by
    have h := congrArg (fun y : D.host.K => D.host.φ₀ (y : D.host.E)) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_sq D)
    rw [← hxs] at h
    push_cast at h
    rw [map_pow] at h
    rw [h, map_neg, map_natCast]
  set ω := Formalism.L2.Th1.CM.omegaK D.host.d with hωdef
  have hom : (2 * ω - 1) ^ 2 = -(D.host.d : ℂ) := by
    rw [hωdef]; unfold Formalism.L2.Th1.CM.omegaK
    have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    linear_combination (-1 : ℂ) * hsq + (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2) * Complex.I_sq
  have hconjω : starRingEnd ℂ ω = 1 - ω := by
    rw [hωdef]; unfold Formalism.L2.Th1.CM.omegaK
    simp only [map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have h2E : ((2 : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : D.host.K) = 1 + 1 by norm_num]; push_cast; norm_num
  have hωφ : D.host.φ₀ ((ωK : D.host.K) : D.host.E) = (1 + D.host.φ₀ (xs : D.host.E)) / 2 := by
    rw [hω]; push_cast; simp only [map_div₀, map_add, map_one]; rw [h2E, map_ofNat]
  have hc : ∀ k : ℤ, ((k : 𝓞 D.host.K) : D.host.K) = (k : D.host.K) := fun k => by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast]
  obtain ⟨m, n, rfl⟩ := hspan a
  have ea : (((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K) =
      (m : D.host.K) + (n : D.host.K) * (ωK : D.host.K) := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, map_intCast,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap]
  set z : ℂ := D.host.φ₀ ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K) : D.host.E) with hz
  have hzv : z = (m : ℂ) + (n : ℂ) * D.host.φ₀ ((ωK : D.host.K) : D.host.E) := by
    rw [hz, ea]; push_cast; simp only [map_add, map_mul, map_intCast]
  have hzb : D.host.φ₀ (D.host.conj ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K) : D.host.E)) =
      starRingEnd ℂ z := Formalism.BasicNotions.Examples₂.emb_conj D.host D.host.φ₀ _
  have hpair : ∃ m' n' : ℤ, z = (m' : ℂ) + (n' : ℂ) * ω ∧ starRingEnd ℂ z = (m' : ℂ) + (n' : ℂ) * (1 - ω) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans hom.symm) with h | h
    · have e : D.host.φ₀ ((ωK : D.host.K) : D.host.E) = ω := by rw [hωφ, h]; ring
      refine ⟨m, n, by rw [hzv, e], ?_⟩
      rw [hzv, e, map_add, map_mul, map_intCast, map_intCast, hconjω]
    · have e : D.host.φ₀ ((ωK : D.host.K) : D.host.E) = 1 - ω := by rw [hωφ, h]; ring
      refine ⟨m + n, -n, by rw [hzv, e]; push_cast; ring, ?_⟩
      rw [hzv, e, map_add, map_mul, map_intCast, map_intCast, map_sub, map_one, hconjω]; push_cast; ring
  obtain ⟨m', n', hz1, hz2⟩ := hpair
  have hcτ : tauK D g.lam ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K)) = ι z :=
    (Formalism.L2.KerInert.lamCIota p g.lam ι hι).1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _)
  have hcbτ : tauKc D g.lam ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K)) =
      ι (starRingEnd ℂ z) := by
    unfold tauKc
    rw [← hzb]
    exact (Formalism.L2.KerInert.lamCIota p g.lam ι hι).1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _)
  rw [hcτ, hcbτ]
  set k : ℕ := (D.host.d + 1) / 4 with hk
  have hq := ReciprocityTheory.ChartRestriction.L1.omegaK_quad D.host.d hd4
  have hN : ι z * ι (starRingEnd ℂ z) = (((m' ^ 2 + m' * n' + n' ^ 2 * (k : ℤ) : ℤ)) : ℂ_[p]) := by
    rw [← map_mul, hz2, hz1, ← map_intCast ι]
    congr 1
    push_cast
    linear_combination (-(n' : ℂ) ^ 2) * hq
  have hmem : (ι z, ι (starRingEnd ℂ z)) ∈ Formalism.L2.Th1.Top.pairsK D.host.d p ι := by
    refine subset_closure ⟨(m', n'), ?_⟩
    show (ι ((m' : ℂ) + (n' : ℂ) * ω), ι ((m' : ℂ) + (n' : ℂ) * (1 - ω))) = (ι z, ι (starRingEnd ℂ z))
    rw [hz2, hz1]
  obtain ⟨-, -, hpairs, -⟩ := Formalism.L2.Th1.Top.calcP D.host.d L hd4 hcmby p h5 ι hIC
  obtain ⟨hE0, hPN0, -⟩ := hpairs _ _ hmem
  have hT := phNormAt_varChange W0 hcoef0 g.C hu.le hui.le hr hs ht (ι (Formalism.L2.Th1.F.s2 L)) _ _ _ hN hE0 hPN0
  rw [← hgW] at hT

  have hser : sgSer g.lam g.abelian₂ = Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [hLg]; exact Formalism.L2.KerInert.Sigma.sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl
  have hwp : Formalism.L2.Th1.A.wpReg g.W =
      PowerSeries.C (ε ^ 2) * PowerSeries.rescale ε (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [Formalism.L2.KerInert.Sigma.wpReg_eq, c2, c3]
    exact (Formalism.L2.Th1.F.seriesScale ℂ_[p] (g.lam a2) (g.lam a3) ε).2.2.2.1
  have hR : PowerSeries.rescale ε (sgSer g.lam g.abelian₂) =
      PowerSeries.C ε * Formalism.L2.Th1.B.sgW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) := by
    unfold Formalism.L2.Th1.B.sgW
    rw [hser, hwp, hιs]
    exact ((Formalism.L2.Th1.F.sigmaScale ℂ_[p] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) ε).2).symm
  have hph : g.ph = Formalism.L2.Th1.B.phW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) :=
    Formalism.L2.KerInert.Dict.formal_phase_agree p g _ hOk hR

  have hX : (g.phAt (Xv ()) : MvPowerSeries Unit ℂ_[p]) = g.ph := PowerSeries.X_subst g.ph
  have hM : (g.phAt (g.mulBy (ι z) (Xv ())) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.subst (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (ι z)) g.ph := by
    unfold G1.phAt; rw [mulBy_g g hOk]
  rw [hM, hX, hph]
  have hsm : (MvPowerSeries.C (ι z * ι (starRingEnd ℂ z)) *
      Formalism.L2.Th1.B.phW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) : MvPowerSeries Unit ℂ_[p]) =
      ((ι z * ι (starRingEnd ℂ z)) • Formalism.L2.Th1.B.phW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) : ℂ_[p]⟦X⟧) := by
    rw [PowerSeries.smul_eq_C_mul]; rfl
  rw [hsm]
  obtain ⟨h0, h1⟩ := hT
  refine ⟨h0, ?_⟩
  rw [Formalism.L2.KerInert.Dict.expMv_eq_mvExp h0]
  intro e
  exact h1 e

end Main

end Formalism.L2.KerInert.PN

namespace Formalism.L2.KerInert

theorem phi_norm_inert_prime : PhNormOKInert := PN.phNormOKInert_of

end Formalism.L2.KerInert
