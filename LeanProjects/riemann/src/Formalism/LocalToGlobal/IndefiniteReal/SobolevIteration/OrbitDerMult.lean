import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.IsLowPairZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult MeasureTheory

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical in

def OrbitDerMult (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {Ss : D.what₂.Tau → SPar} (M : DSModel V Ss)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T →
    ∀ τ, ∀ X ∈ lieAt V τ, ∀ (v : M.Vec) (w : M.sm τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v τ)) (w : M.H τ) 0 →
      ∀ x, HasDerivAt (fun t : ℝ => T v (x * oneP θ V τ X t)) (T (Function.update v τ w) x) 0

end Formalism.IndefR.Tow

end
