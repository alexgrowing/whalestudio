import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelCondition

noncomputable section

namespace Formalism.L2.KerInert.BeCob

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1 ModelOverW)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Integral)

def eLT {l : ℕ} [Fact l.Prime] {g : G1 l} (hLT : LTIso g) : ℂ_[l] := wToC l (epOf hLT : WW l)

def vLT {l : ℕ} [Fact l.Prime] {g : G1 l} (hLT : LTIso g) : PowerSeries ℂ_[l] :=
  PowerSeries.subst (PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l) g.ex

def psiLT {l : ℕ} [Fact l.Prime] {g : G1 l} (hLT : LTIso g) : PowerSeries ℂ_[l] :=
  PowerSeries.subst (vLT hLT) g.ph

def CobExact : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (g : G1 l) (hLT : LTIso g), g.Ok → BeRat g (eLT hLT) →
    ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
      MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)) =
        cob (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F) (psiLT hLT)

def CobSimeq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K),
    MvPowerSeries.constantCoeff F = 0 → Integral F →
    ∀ f f' : PowerSeries K, Formalism.InvariantFactorPaths.G7.Simeq (f : MvPowerSeries Unit K) f' →
      Formalism.InvariantFactorPaths.G7.Simeq (cob F f) (cob F f')

def PhTie : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (g : G1 l) (hLT : LTIso g), g.Ok → ∀ s2 : ℂ_[l],
    g.ph = Formalism.L2.Th1.B.phW g.W s2 →
    Formalism.InvariantFactorPaths.G7.Simeq (psiLT hLT : MvPowerSeries Unit ℂ_[l])
      (phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 (eLT hLT)⁻¹)

def ThetaTie : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (g : G1 l) (hLT : LTIso g), g.Ok →
    ∀ n, ‖PowerSeries.coeff n (thetaS l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) (eLT hLT)⁻¹)‖ ≤ 1

def BeCoef : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ModelOverW g.lam g.abelian₂ g.C → Formalism.MainNotions.GL3Theta.CoefWf g.ph →
    Formalism.MainNotions.GL3Theta.CoefWf (g.be (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) ℂ_[l])

def ShortIso : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K], ‖(2 : K)‖ = 1 → ‖(3 : K)‖ = 1 →
    ∀ W : WeierstrassCurve K, Formalism.L2.Th1.A.IntModel W →
      Integral (PowerSeries.subst (Formalism.L2.Th1.A.logSer W)
        (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W))) : MvPowerSeries Unit K)

end Formalism.L2.KerInert.BeCob
