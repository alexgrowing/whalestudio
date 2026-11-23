import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SqrtInUnramifiedCompletion

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.L2.Th1.G (linSub sqSum betaPair)
open Formalism.L2.Th1.D (GaussNormEstimates.normZ_lt GaussNormEstimates.normZ_one)
open Formalism.G (unitBall)

namespace CAux

variable {p : ℕ} [Fact p.Prime]

theorem coeffIn {W : WeierstrassCurve ℂ_[p]} (h : IntCurve W) :
    Formalism.L2.Th1.C.CoeffIn (unitBall ℂ_[p]) W :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem norm_two (h2 : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have h : ¬ (p : ℤ) ∣ (2 : ℤ) := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have := Formalism.L2.Th1.D.GaussNormEstimates.normZ_one (l := p) h
  simpa using this

theorem ne_two {dK : ℕ} (hmod : dK % 4 = 3) (hd : p ∣ dK) : p ≠ 2 := by
  rintro rfl
  omega

theorem norm_d_lt {dK : ℕ} (hd : p ∣ dK) : ‖(dK : ℂ_[p])‖ < 1 := by
  have h : (p : ℤ) ∣ (dK : ℤ) := by exact_mod_cast hd
  have := (Formalism.L2.Th1.D.GaussNormEstimates.normZ_lt (l := p)).2 h
  simpa using this

theorem d_ne {dK : ℕ} (hmod : dK % 4 = 3) : (dK : ℂ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

theorem norm_d_eq {dK : ℕ} (hsq : Squarefree dK) (hd : p ∣ dK) : ‖(dK : ℂ_[p])‖ = ‖(p : ℂ_[p])‖ := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, rfl⟩ := hd
  have hm : ¬ p ∣ m := by
    intro h
    obtain ⟨k, rfl⟩ := h
    have h1 : p * p ∣ p * (p * k) := ⟨k, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p h1))
  have h : ¬ (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hm
  have h1 := Formalism.L2.Th1.D.GaussNormEstimates.normZ_one (l := p) h
  rw [Nat.cast_mul, norm_mul]
  have h2 : ‖(m : ℂ_[p])‖ = 1 := by simpa using h1
  rw [h2, mul_one]

theorem frame (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) (hW : IntCurve (curveL p L ι)) :
    Formalism.L2.Th1.C.IsLogPair (logSer (curveL p L ι)) (expSer (curveL p L ι)) ∧
    Formalism.L2.Th1.C.IsOneUnit (unitBall ℂ_[p]) (PowerSeries.derivative ℂ_[p] (logSer (curveL p L ι))) ∧
    PowerSeries.constantCoeff (phC p L ι) = 0 := by
  obtain ⟨hlp, -, -, -, hu⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[p] (unitBall ℂ_[p]) _ (coeffIn hW)
  exact ⟨hlp, hu, (Formalism.L2.Th1.C.phOIsPh ℂ_[p] _ _ _ hlp.1 hlp.2.1).2.1⟩

end CAux

open CAux

theorem ShapeOrthD_of (hS : ShapeCM) (hK : KernelJoint) : ShapeOrthD := by
  intro dK L _ hmod hcm p _ hd ι hW H _ _ N0 N1 n _ A u th Q2 hA hth _ hQ0 hQ hid ω₀ hω hω2 κ _ r s N hr
    hN hpN hs
  obtain ⟨hlp, hu, hph0⟩ := frame L ι hW
  have hSh := hS dK L hmod hcm p hd ι hW
  obtain ⟨G, hG, hΘ⟩ := hK p L ι (ne_two hmod hd) hW n ω₀ hω hω2 κ r s N hr hN hpN hs
  refine ⟨hSh.1, ?_⟩
  rw [hΘ]
  exact Formalism.L2.Th1.G.kernelShape ℂ_[p] _ _ _ dK hlp hu hph0 hSh (d_ne hmod) H N0 N1 n (fun _ => 1) A u th Q2
    (norm_two (ne_two hmod hd)) (fun _ => by simp) hA hth hQ0 hQ hid G hG

theorem ThmBOrth_of (hS : ShapeCM) (hK : KernelJoint) : ThmBOrth := by
  intro dK L _ hmod hcm p _ hd ι hW H _ _ N0 N1 n _ A u th Q2 hA hth hu1 hQ0 hQ hid ω₀ hω hω2 κ _ r s N hr
    hN hpN hs
  obtain ⟨hlp, hu, hph0⟩ := frame L ι hW
  have hSh := hS dK L hmod hcm p hd ι hW
  obtain ⟨G, hG, hΘ⟩ := hK p L ι (ne_two hmod hd) hW n ω₀ hω hω2 κ r s N hr hN hpN hs
  rw [hΘ]
  exact Formalism.L2.Th1.G.kernelThmB ℂ_[p] _ _ _ dK hlp hu hph0 hSh (norm_pos_iff.mpr (d_ne hmod)) (norm_d_lt hd)
    H N0 N1 n (fun _ => 1) A u th Q2 (norm_two (ne_two hmod hd)) (fun _ => by simp) hA hth hu1 hQ0 hQ hid G hG

theorem ThmBGaussOrth_of (hS : ShapeCM) (hK : KernelJoint) : ThmBGaussOrth := by
  intro dK L hsq hmod hcm p _ hd ι hW H _ _ N0 N1 n _ A u th Q2 hA hth hu1 hQ0 hQ hid ω₀ hω hω2 κ _ r s N hr
    hN hpN hs
  obtain ⟨hlp, hu, hph0⟩ := frame L ι hW
  have hSh := hS dK L hmod hcm p hd ι hW
  have hSh' : Formalism.L2.Th1.G.ShapeAt (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) p := by
    refine ⟨?_, hSh.2⟩
    rw [← norm_d_eq hsq hd]
    exact hSh.1
  obtain ⟨G, hG, hΘ⟩ := hK p L ι (ne_two hmod hd) hW n ω₀ hω hω2 κ r s N hr hN hpN hs
  rw [hΘ]
  exact Formalism.L2.Th1.G.kernelThmBGauss p _ _ _ hlp hu hph0 hSh'
    H N0 N1 n (fun _ => 1) A u th Q2 (norm_two (ne_two hmod hd)) (fun _ => by simp) hA hth hu1 hQ0 hQ hid G hG

theorem IntOpOrth_of (hJ : JetsCM) (hK : KernelJoint) : IntOpOrth := by
  intro dK L _ hmod hcm p _ h2 hd ι hW n _ ω₀ hω hω2 κ _ r s N hr hN hpN hs
  obtain ⟨hlp, hu, hph0⟩ := frame L ι hW
  obtain ⟨G, hG, hΘ⟩ := hK p L ι h2 hW n ω₀ hω hω2 κ r s N hr hN hpN hs
  rw [hΘ]
  exact Formalism.L2.Th1.G.kernelTwo ℂ_[p] _ _ _ hlp hu hph0 (hJ dK L hmod hcm p h2 hd ι hW) n (fun _ => 1)
    (fun _ => by simp) G hG

end Formalism.L2.Th1.Top
