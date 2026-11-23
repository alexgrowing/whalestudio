import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.SphGal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def BaseChangeDefinite : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (W' W : Submodule ℂ (MMap M)),
    IsInfFam θ → (∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ)) → V.SigOK → V.IsPosDef → IsCuspQuot θ M W' W → HasBaseChange M W' W

end GlobalTheory.SphGal

end
