import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

def IsAdapted {D : D7} (V : HSp D) {m : ℕ} (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, ∃ (k : Formalism.REAL.KG (ε τ)) (S : Set (Fin V.rank)),
    Submodule.span ℂ (Set.range (fun i : upTo T => (fr τ *ᵥ fun j => tauE D τ (X j i))) ∪
        Set.range (fun i : upTo T => (fr τ *ᵥ fun j => tauE D τ (Y j i)))) =
      (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin V.rank) (1 : ℂ) : Fin V.rank → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
