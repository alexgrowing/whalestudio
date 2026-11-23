import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

open Formalism.MainNotions.G Formalism.BasicNotions NumberField Formalism.MainNotions.TaylorLogMetric Classical

noncomputable section

namespace Formalism.MainNotions.G

def tvarOf (D : D7) {p d : ℕ} (Po : Pos D p d) {N N' : ℕ} (j : (Bool × HH D) × Fin N × Fin N') : TVar D Po N N' :=
  (((Equiv.ofBijective _ Po.bij).symm (tauPl D j.1)).2, (((Equiv.ofBijective _ Po.bij).symm (tauPl D j.1)).1, j.2))

def EntLiftSplit {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : Formalism.MainNotions.GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) : Prop :=
  ∃ (d : ℕ) (Po : Pos D (D.what₂.places.resChar w) d)
    (P : ∀ i, (D.chTw u μ).cls i → {v // v ∈ Po.V} → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E),
    (∀ i, i ≤ D.R.m → ∀ c v, LocBasisW D (posEmb D (E.lam w) Po.φ v.1 (0 : ZMod d)) (O.lat i c).1 (P i c v)) ∧
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      ∃ c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w], (∀ τ, ‖c0 τ‖ = 1) ∧
        E.Th u μ w i c c' = atLin (fun k (j : (Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) =>
          c0 k.1 * lamC (E.lam w) (O.dgen k.1) * chg D (E.lam w) Po (P i c) (P (i + 1) c') k (tvarOf D Po j))
            (fun j => MvPowerSeries.X j) (pSer D (E.lam w) (O.Th i c c'))

def EntLiftC {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : Formalism.MainNotions.GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) : Prop :=
  ∃ P : ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E,
    (∀ i, i ≤ D.R.m → ∀ c τ, OrthoBasisW D (tauEmb D (E.lam w) τ) (O.lat i c).1 (P i c τ)) ∧
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      ∃ c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w], (∀ τ, ‖c0 τ‖ = 1) ∧
        E.Th u μ w i c c' = atLin (fun k (j : (Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) =>
          c0 k.1 * lamC (E.lam w) (O.dgen k.1) * chgB D (E.lam w) (P i c) (P (i + 1) c') k
            ((0 : ZMod 1), (tauPl D j.1, j.2))) (fun j => MvPowerSeries.X j) (pSer D (E.lam w) (O.Th i c c'))

def EntLift {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)
    (O : ∀ u μ, Formalism.MainNotions.GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ w, LevFree Dx u μ w → D.what₂.places.resChar w ∉ (O u μ).S ∧
    (AllSplit D (D.what₂.places.resChar w) → EntLiftSplit E u μ (O u μ) w) ∧
    (IsFrobC D (D.what₂.places.resChar w) → EntLiftC E u μ (O u μ) w)

end Formalism.MainNotions.G
