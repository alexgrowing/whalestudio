import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementJ

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

def ShapeDiagram : Prop :=
  ∀ (ν : ℕ) (TT : Finset (ZMod (2 * ν))) (μ : ZMod (2 * ν) → YoungDiagram) (s : ZMod (2 * ν)),
    alG TT (fun s => (μ s).rowLen 0) (fun s c => (μ s).colLen c) s =
        (if s ∈ TT then (μ s).rowLen 0 - (μ s).rowLen 1 else 0) ∧
    capG TT (fun s => (μ s).rowLen 0) (fun s c => (μ s).colLen c) s =
        (if s ∈ TT then (μ s).rowLen 1 else (μ s).rowLen 0)

def EdgeNoTrunc : Prop :=
  ∀ (h r1 i : ℕ) (I : Fin h → Fin r1),
    ((univ.image I) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card ≤ min h i

def ThetaLogIsSubst : Prop :=
  ∀ (K : Type) [Field K] (ν r0 r1 : ℕ) [NeZero ν] (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K)
    (μ : PowerSeries K) (Tht : MvPowerSeries (Bool × EV ν r0 r1) K),
    PowerSeries.constantCoeff μ = 0 →
    thetaLog om oms ϖ μ Tht = MvPowerSeries.subst (fun x => MvPowerSeries.subst
        (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (MvPowerSeries.C ϖ * sSub om oms μ x)) Tht

end Formalism.InvariantFactorPaths.G7
