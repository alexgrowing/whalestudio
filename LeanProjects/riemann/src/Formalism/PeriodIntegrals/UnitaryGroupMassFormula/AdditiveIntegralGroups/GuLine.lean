import Mathlib
import Formalism.PeriodIntegrals.AddIntG

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

def G (W : WeierstrassCurve ℂ_[p]) {R : Type*} [CommRing R] [Algebra ℂ_[p] R] (u v : R) : R :=
  u ^ 3 + algebraMap ℂ_[p] R W.a₁ * u * v + algebraMap ℂ_[p] R W.a₂ * u ^ 2 * v +
    algebraMap ℂ_[p] R W.a₃ * v ^ 2 + algebraMap ℂ_[p] R W.a₄ * u * v ^ 2 +
    algebraMap ℂ_[p] R W.a₆ * v ^ 3 - v

def Gu (W : WeierstrassCurve ℂ_[p]) {R : Type*} [CommRing R] [Algebra ℂ_[p] R] (u v : R) : R :=
  3 * u ^ 2 + algebraMap ℂ_[p] R W.a₁ * v + 2 * algebraMap ℂ_[p] R W.a₂ * u * v +
    algebraMap ℂ_[p] R W.a₄ * v ^ 2

def Gv (W : WeierstrassCurve ℂ_[p]) {R : Type*} [CommRing R] [Algebra ℂ_[p] R] (u v : R) : R :=
  algebraMap ℂ_[p] R W.a₁ * u + algebraMap ℂ_[p] R W.a₂ * u ^ 2 + 2 * algebraMap ℂ_[p] R W.a₃ * v +
    2 * algebraMap ℂ_[p] R W.a₄ * u * v + 3 * algebraMap ℂ_[p] R W.a₆ * v ^ 2 - 1

def wser (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] := PowerSeries.X ^ 3 * wq

def wv (wq : PowerSeries ℂ_[p]) (i : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p] :=
  PowerSeries.subst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) (wser wq)

def lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  fun e => PowerSeries.coeff (e 0 + e 1 + 1) (wser wq)

def nu (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  wv wq 0 - lam wq * Xv 0

abbrev cc (a : ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] := algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) a

def Acf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  1 + cc W.a₂ * lam wq + cc W.a₄ * lam wq ^ 2 + cc W.a₆ * lam wq ^ 3

def Bcf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  cc W.a₁ * lam wq + cc W.a₂ * nu wq + cc W.a₃ * lam wq ^ 2 + 2 * cc W.a₄ * lam wq * nu wq +
    3 * cc W.a₆ * lam wq ^ 2 * nu wq

def Ccf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  cc W.a₁ * nu wq + 2 * cc W.a₃ * lam wq * nu wq + cc W.a₄ * nu wq ^ 2 +
    3 * cc W.a₆ * lam wq * nu wq ^ 2 - lam wq

def Dcf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  cc W.a₃ * nu wq ^ 2 + cc W.a₆ * nu wq ^ 3 - nu wq

def Z3 (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  -Xv 0 - Xv 1 - Bcf W wq * (Acf W wq)⁻¹

def Fch (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then (0 : MvPowerSeries (Fin 2) ℂ_[p]) else Z3 W wq) (Z3 W wq)

end PI.AddIntG.Wk
