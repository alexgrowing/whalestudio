import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.KerStd

def StdBases (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  (∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) ∧
  ((IsResidueClassZero D p ∨ IsSg D p) → ∀ z : Bool × HH D,
    ((P (tauPl D (posPl D p z 1))).map D.host.conj).transpose * P (tauPl D z) = 1) ∧
  (p = D.host.d → DualB D P)

def stdSer (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ} (κ : D.what₂.Tau → ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p] :=
  atLin (fun k (j : (Bool × HH D) × Fin N × Fin N') =>
    κ k.1 * chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) (fun j => MvPowerSeries.X j) F

def StdScal (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (s : D.what₂.Tau → ℂ) (κ : D.what₂.Tau → ℂ_[p]) : Prop :=
  (∀ τ, ‖κ τ‖ = ‖lamC lam (s τ)‖) ∧ ((IsResidueClassZero D p ∨ IsSg D p) → ∀ τ, κ τ = 1)

abbrev ThFam (D : D7) : Type :=
  ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) →
    MvPowerSeries ((Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w]

def ThStd {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)
    (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (Th : ThFam D) : Prop :=
  ∀ u μ w, LevFree Dx u μ w →
    ∃ (P : ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
      (κ : D.what₂.Tau → ℂ_[D.what₂.places.resChar w]),
      (∀ i, i ≤ D.R.m → ∀ c, StdBases D (E.lam w) ((O u μ).lat i c).1 (P i c)) ∧
      StdScal D (E.lam w) (O u μ).dgen κ ∧
      ∀ i, i < D.R.m → ∀ c c', Th u μ w i c c' =
        stdSer D (E.lam w) κ (P i c) (P (i + 1) c') (pSer D (E.lam w) ((O u μ).Th i c c'))

end GlobalTheory.KerStd
