import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions

def PullSchLI : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r n : ℕ) (c : Matrix (Fin r) (Fin n) D.host.E), LinearIndependent D.host.E c →
    ∀ φ : Mx D m n → ℂ, φ ∈ schwartzA θ m n → pull c φ ∈ schwartzA θ m r

end PositivityTheory.GramSchwartzFunctions
