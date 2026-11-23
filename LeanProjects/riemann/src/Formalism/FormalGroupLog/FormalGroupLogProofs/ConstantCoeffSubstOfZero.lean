import Formalism.FormalGroupLog.Statement
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

open MvPowerSeries

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

theorem hs2 {σ : Type*} {u v : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) : MvPowerSeries.HasSubst ![u, v] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hu, hv])

theorem hs3 {σ : Type*} {u v w : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) (hw : constantCoeff w = 0) : MvPowerSeries.HasSubst ![u, v, w] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hu, hv, hw])

theorem subst2_subst {σ τ : Type*} (Φ : MvPowerSeries (Fin 2) R) {u v : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) {b : σ → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) :
    (Φ.subst ![u, v]).subst b = Φ.subst ![u.subst b, v.subst b] := by
  rw [MvPowerSeries.subst_comp_subst_apply (hs2 hu hv) hb]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem psubst_subst {σ τ : Type*} (φ : PowerSeries R) {u : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (φ.subst u).subst b = φ.subst (u.subst b) := by
  have hu' : MvPowerSeries.HasSubst (fun _ : Unit => u) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hu' hb]

theorem constantCoeff_subst_of_zero {σ τ : Type*} [Finite σ] [Finite τ]
    (Φ : MvPowerSeries σ R) {b : σ → MvPowerSeries τ R} (hb : ∀ i, constantCoeff (b i) = 0) :
    constantCoeff (Φ.subst b) = constantCoeff Φ := by
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [MvPowerSeries.constantCoeff_subst hb', finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : constantCoeff (d.prod fun s e => b s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, hb i, zero_pow hi]
    rw [h0, smul_zero]

theorem isUnit_natCast_succ [Algebra ℚ R] (n : ℕ) : IsUnit ((n : R) + 1) := by
  have h : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) := by simp
  rw [h]
  exact IsUnit.map _ (isUnit_iff_ne_zero.2 (by positivity))

variable (F : FormalGroup R)

def omegaF : PowerSeries R :=
  MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0]
    (MvPowerSeries.pderiv R 1 F.toPowerSeries)

theorem constantCoeff_omega : PowerSeries.constantCoeff (omegaF F) = 1 := by
  have := constantCoeff_subst_of_zero (MvPowerSeries.pderiv R 1 F.toPowerSeries)
    (b := ![(PowerSeries.X : PowerSeries R), 0]) (fun i => by fin_cases i <;> simp [PowerSeries.X])
  rw [omegaF, PowerSeries.constantCoeff, this, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simpa using F.lin_coeff_Y

theorem hb0 : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries R), 0] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [PowerSeries.X])

theorem hX0 : constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = 0 := by
  simp
theorem hX1 : constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = 0 := by
  simp

theorem eval_zero_subst_law (φ : PowerSeries R) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (φ.subst F.toPowerSeries) = φ := by
  rw [psubst_subst φ F.zero_constantCoeff hb0]
  have : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] F.toPowerSeries =
      PowerSeries.X := F.Xzero_eq_X
  rw [this, PowerSeries.X_subst]

theorem evalYZero_atY (φ : PowerSeries R) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (atY φ) =
      PowerSeries.C (PowerSeries.constantCoeff φ) := by
  rw [atY, psubst_subst φ hX1 hb0, subst_X hb0]
  simp [PowerSeries.subst_zero_eq_C_constantCoeff]
  rfl

theorem pderiv_log {g : PowerSeries R} (hg : IsLog F g) :
    (PowerSeries.derivative R g).subst F.toPowerSeries * MvPowerSeries.pderiv R 1 F.toPowerSeries =
      atY (PowerSeries.derivative R g) := by
  have := congrArg (MvPowerSeries.pderiv R 1) hg.2.2
  rw [pderiv_psubst F.zero_constantCoeff, map_add, atX, atY, pderiv_psubst hX0,
    pderiv_psubst hX1] at this
  simpa [pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)] using this

theorem derivative_log_mul_omega {g : PowerSeries R} (hg : IsLog F g) :
    PowerSeries.derivative R g * omegaF F = 1 := by
  have := congrArg (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0]) (pderiv_log F hg)
  rw [subst_mul hb0, eval_zero_subst_law, evalYZero_atY] at this
  rw [omegaF, this]
  have h1 : PowerSeries.constantCoeff (PowerSeries.derivative R g) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, hg.2.1]
    simp
  rw [h1, map_one]

theorem log_unique [Algebra ℚ R] {f g : PowerSeries R} (hf : IsLog F f) (hg : IsLog F g) :
    f = g := by
  have hd : PowerSeries.derivative R f = PowerSeries.derivative R g := by
    have hu := PowerSeries.mul_invOfUnit (omegaF F) 1 (by simp [constantCoeff_omega])
    calc PowerSeries.derivative R f
        = PowerSeries.derivative R f * omegaF F * PowerSeries.invOfUnit (omegaF F) 1 := by
          rw [mul_assoc, hu, mul_one]
      _ = PowerSeries.derivative R g * omegaF F * PowerSeries.invOfUnit (omegaF F) 1 := by
          rw [derivative_log_mul_omega F hf, derivative_log_mul_omega F hg]
      _ = PowerSeries.derivative R g := by rw [mul_assoc, hu, mul_one]
  ext n
  cases n with
  | zero => simpa using hf.1.trans hg.1.symm
  | succ n =>
    have := congrArg (PowerSeries.coeff n) hd
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at this
    exact (isUnit_natCast_succ (R := R) n).mul_left_cancel (by
      rw [mul_comm, this, mul_comm])

end Formalism.G.LogP

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

theorem subst_zero' {σ τ : Type*} {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (0 : MvPowerSeries σ R).subst b = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom hb, map_zero]

theorem subst_XX (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = Φ := by
  have h : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = MvPowerSeries.X := by
    funext i
    fin_cases i <;> rfl
  rw [h, MvPowerSeries.subst_self, id]

theorem omega_subst {σ : Type*} {u : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (F : FormalGroup R) :
    (omegaF F).subst u = (MvPowerSeries.pderiv R 1 F.toPowerSeries).subst ![u, 0] := by
  have hu' : MvPowerSeries.HasSubst (fun _ : Unit => u) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)
  unfold omegaF
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hb0 hu']
  congr 1
  funext i
  fin_cases i
  · exact MvPowerSeries.subst_X hu' ()
  · exact subst_zero' hu'

variable (F : FormalGroup R)

theorem omega_key :
    (omegaF F).subst F.toPowerSeries =
      MvPowerSeries.pderiv R 1 F.toPowerSeries * atY (omegaF F) := by
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hY : ∀ i, constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = 0 := fun i => by
    simp
  have hG : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1]) = 0 := by
    rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]
  have hH : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 2]) = 0 := by
    rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]
  have dG : MvPowerSeries.pderiv R 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1]) = 0 := by
    rw [pderiv_subst (fun i => by fin_cases i <;> simp)]
    simp [Fin.sum_univ_two, pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide),
      pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
  have dH : MvPowerSeries.pderiv R 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 2]) = (MvPowerSeries.pderiv R 1 F.toPowerSeries).subst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2] := by
    rw [pderiv_subst (fun i => by fin_cases i <;> simp)]
    simp [Fin.sum_univ_two, pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
  have E := congrArg (MvPowerSeries.pderiv R 2) F.assoc
  rw [pderiv_subst (fun i => by fin_cases i <;> simp [hG]),
    pderiv_subst (fun i => by fin_cases i <;> simp [hH])] at E
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, dG, dH, pderiv_X_self,
    pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide), mul_zero, zero_add, mul_one] at E
  have hc3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0] :=
    hs3 (by simp) (by simp) (by simp)
  have E' := congrArg (MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0]) E
  rw [subst_mul hc3, subst2_subst _ hG (hY 2) hc3, subst2_subst _ (hY 0) hH hc3,
    subst2_subst _ (hY 1) (hY 2) hc3, subst2_subst _ (hY 0) (hY 1) hc3,
    subst2_subst _ (hY 1) (hY 2) hc3] at E'
  simp only [subst_X hc3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at E'
  rw [subst_XX, F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero hX1), subst_XX] at E'
  rw [omega_subst hFc, atY, omega_subst hX1]
  exact E'

end Formalism.G.LogP

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

theorem psubst_one {σ : Type*} {a : MvPowerSeries σ R} (ha : PowerSeries.HasSubst a) :
    (1 : PowerSeries R).subst a = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

theorem subst_X0_zero_eq_rescale (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = rescale ![1, 0] Φ := by
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  fin_cases s <;> simp

theorem eq_zero_of_pderiv_one [Algebra ℚ R] {h : MvPowerSeries (Fin 2) R}
    (hD : MvPowerSeries.pderiv R 1 h = 0)
    (h0 : h.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0) : h = 0 := by
  rw [subst_X0_zero_eq_rescale] at h0
  ext n
  rw [map_zero]
  by_cases hn : n 1 = 0
  · have h1 := congrArg (MvPowerSeries.coeff n) h0
    rw [MvPowerSeries.coeff_rescale, map_zero] at h1
    have hprod : (n.prod fun s m => (![1, 0] : Fin 2 → R) s ^ m) = 1 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_one
      intro s hs
      fin_cases s
      · simp
      · exact absurd hn (Finsupp.mem_support_iff.mp hs)
    rw [hprod, one_mul] at h1
    exact h1
  · have hm : n = (n - Finsupp.single 1 1) + Finsupp.single 1 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    have h1 := congrArg (MvPowerSeries.coeff (n - Finsupp.single 1 1)) hD
    rw [MvPowerSeries.coeff_pderiv, map_zero, ← hm] at h1
    have hu : IsUnit ((((n - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 : ℕ) : R) + 1) := isUnit_natCast_succ _
    exact (hu.mul_left_eq_zero).mp h1

variable (F : FormalGroup R)

def lam : PowerSeries R := PowerSeries.invOfUnit (omegaF F) 1

theorem omega_mul_lam : omegaF F * lam F = 1 := by
  exact PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_omega, Units.val_one])

variable [Algebra ℚ R]

def logF : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 0 else
    algebraMap ℚ R (1 / (n : ℚ)) * PowerSeries.coeff (n - 1) (lam F)

theorem derivative_logF : PowerSeries.derivative R (logF F) = lam F := by
  ext n
  rw [PowerSeries.coeff_derivative]
  unfold logF
  rw [PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, mul_comm, ← mul_assoc]
  have h : ((n : R) + 1) * algebraMap ℚ R (1 / ((n + 1 : ℕ) : ℚ)) = 1 := by
    rw [show ((n : R) + 1) = algebraMap ℚ R ((n + 1 : ℕ) : ℚ) by simp, ← map_mul,
      mul_one_div_cancel (by positivity), map_one]
  rw [h, one_mul]

theorem logF_isLog : IsLog F (logF F) := by
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hFs : PowerSeries.HasSubst F.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero hFc
  have hX1s : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hX1
  have hc0 : PowerSeries.constantCoeff (logF F) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk, if_pos rfl]
  refine ⟨hc0, ?_, ?_⟩
  · rw [logF, PowerSeries.coeff_mk, if_neg one_ne_zero, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, lam, PowerSeries.constantCoeff_invOfUnit]
    simp
  · have hω := omega_mul_lam F
    have hF1 : (lam F).subst F.toPowerSeries * (omegaF F).subst F.toPowerSeries = 1 := by
      rw [← PowerSeries.subst_mul hFs, mul_comm, hω, psubst_one hFs]
    have hY1 : atY (lam F) * atY (omegaF F) = 1 := by
      rw [atY, atY, ← PowerSeries.subst_mul hX1s, mul_comm, hω, psubst_one hX1s]
    have hk := omega_key F
    have hD : MvPowerSeries.pderiv R 1
        ((logF F).subst F.toPowerSeries - atX (logF F) - atY (logF F)) = 0 := by
      rw [map_sub, map_sub, pderiv_psubst hFc, atX, atY, pderiv_psubst hX0, pderiv_psubst hX1,
        derivative_logF, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      linear_combination (-((lam F).subst F.toPowerSeries *
        MvPowerSeries.pderiv R 1 F.toPowerSeries)) * hY1 + atY (lam F) * hF1 -
        (lam F).subst F.toPowerSeries * atY (lam F) * hk
    have hc2 : MvPowerSeries.HasSubst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] := hs2 (by simp) (by simp)
    have h0 : ((logF F).subst F.toPowerSeries - atX (logF F) - atY (logF F)).subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0 := by
      rw [subst_sub hc2, subst_sub hc2, atX, atY, psubst_subst _ hFc hc2, psubst_subst _ hX0 hc2,
        psubst_subst _ hX1 hc2, F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero hX0),
        subst_X hc2, subst_X hc2]
      simp [PowerSeries.subst_zero_of_constantCoeff_zero hc0]
    have := eq_zero_of_pderiv_one hD h0
    rw [sub_sub, sub_eq_zero] at this
    exact this

end Formalism.G.LogP

namespace Formalism.G.LogP

variable {R : Type*} [CommRing R]

theorem psubst_injective {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : PowerSeries.coeff 1 f = 1) {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (h : f.subst a = f.subst b) : a = b := by
  have : Invertible (PowerSeries.coeff 1 f) := hf1 ▸ invertibleOne
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have inv : ∀ c : MvPowerSeries σ R, constantCoeff c = 0 → f.substInv.subst (f.subst c) = c := by
    intro c hc
    have hcs : PowerSeries.HasSubst c := PowerSeries.HasSubst.of_constantCoeff_zero hc
    rw [← PowerSeries.subst_comp_subst_apply hfs hcs, PowerSeries.subst_substInv_left f hf0,
      PowerSeries.subst_X hcs]
  rw [← inv a ha, h, inv b hb]

end Formalism.G.LogP

theorem Formalism.G.log_exists_unique : Formalism.G.LogExistsUnique := by
  intro R _ _ F
  exact ⟨Formalism.G.LogP.logF F, Formalism.G.LogP.logF_isLog F,
    fun g hg => Formalism.G.LogP.log_unique F hg (Formalism.G.LogP.logF_isLog F)⟩

theorem Formalism.G.is_comm_of_rat : Formalism.G.IsCommOfRat := by
  intro R _ _ F
  refine ⟨?_⟩
  have hf := Formalism.G.LogP.logF_isLog F
  set f := Formalism.G.LogP.logF F
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hc : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] :=
    Formalism.G.LogP.hs2 (by simp) (by simp)
  have hFs : constantCoeff (F.toPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]
  have h1 : f.subst (F.toPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) =
      f.subst F.toPowerSeries := by
    rw [← Formalism.G.LogP.psubst_subst f hFc hc, hf.2.2, subst_add hc, Formalism.G.atX, Formalism.G.atY,
      Formalism.G.LogP.psubst_subst f Formalism.G.LogP.hX0 hc, Formalism.G.LogP.psubst_subst f Formalism.G.LogP.hX1 hc,
      subst_X hc, subst_X hc]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [add_comm]
  exact (Formalism.G.LogP.psubst_injective hf.1 hf.2.1 hFs hFc h1).symm
