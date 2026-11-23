import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinCuspApprox

variable {D : D7}

abbrev avgN (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e φ

def KStab (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (s : Set D.what₂.Tau) (W : Submodule ℂ (GA D N.V → ℂ)) : Prop :=
  ∀ τ ∈ s, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), N.M.fr τ * g * (N.M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (N.M.ε τ) →
    ∀ f ∈ W, rTr N.V (atTau θ N.V τ g) f ∈ W

theorem kStab_empty (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (W : Submodule ℂ (GA D N.V → ℂ)) : KStab θ N ∅ W := fun _ h => h.elim

end GlobalTheory.KFinCuspApprox

end
