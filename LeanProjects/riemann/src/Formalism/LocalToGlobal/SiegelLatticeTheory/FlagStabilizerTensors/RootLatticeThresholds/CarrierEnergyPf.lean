import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergy
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def IntNX (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : ℝ :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
            (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
              (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
    ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * (IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D))

def LocRep (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) : Prop :=
  (∀ v, Measurable (L v) ∧ ∀ cv, 0 ≤ L v cv) ∧
    ∀ c ∈ Good X u u', ∀ v, hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v (c v)

def PlaceEnergy (P : Parts X u u') (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  ∀ v, Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v)) ≠ ⊤ ∧
    ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) =
      ENNReal.ofReal (K v * (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal)

def ConstPin (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  (∀ v, 0 ≤ K v) ∧
    (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
              (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
                (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
      ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * ((∏ v, K v) / Formalism.L2.SG.MassDataConc.kapN D)) =
      (P.Gam0 ^ P.S.f)⁻¹

end Formalism.L2.SG.Pf.Carrier.EnergyPf
