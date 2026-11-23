import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyConst

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPlace

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def lamA (P : Parts X u u') (a : Fin P.S.G.r) : ℝ := ((P.S.g : ℝ) / (2 * Real.pi)) ^ (2 * (P.S.G.r - a.val))

def phiQ (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (cv : Fin (D.R.rS + 1) → ℂ) : (Fin P.S.G.r → ℂ) × ℂ :=
  (fun a => ((lamA P a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩, cv ⟨D.R.rS, by omega⟩)

def K0 (P : Parts X u u') : ℝ :=
  2 ^ (P.S.G.r + 1) * ∏ a : Fin P.S.G.r, (lamA P a ^ (2 * (Formalism.QuantumDeterminants.Mdim P.S.G.k P.S.G.r a - 1)))⁻¹

def PlaceNorm (P : Parts X u u') (hr : P.S.G.r = D.R.rS)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) : Prop :=
  ∀ v, ∀ cv ∈ GoodV u u', L v cv =
    ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
      (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖ ^ 2

def ChangeVar (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  P.S.G.k = D.R.k →
    (∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u') →
    ∀ v (F : (Fin P.S.G.r → ℂ) × ℂ → ℝ), (∀ q, 0 ≤ F q) →
      ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * F (phiQ P hr cv)) ∂(dcV (D := D)) =
        ENNReal.ofReal (K0 P) * ∫⁻ q, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight P.S.G.k P.S.G.r
          (Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z)
          (Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z') q * F q)

def NormFin (P : Parts X u u') : Prop := ∀ j, Formalism.FourierDecayAlt.B.normSq (P.T j).base (P.f j) ≠ ⊤

def KMatch (P : Parts X u u') : Prop :=
  (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) → Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE → P.S.G.r = D.R.rS →
    P.S.G.k = D.R.k → 0 < P.S.g → 1 ≤ P.S.G.k → K0 P = EnergyConst.Kexp P

end Formalism.L2.SG.Pf.Carrier.EnergyPlace
