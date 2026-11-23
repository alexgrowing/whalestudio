import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory

theorem pi_muNl_eq_dnB_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (A : Set X.B.I.Ginf), 0 < θ → MeasurableSet A → Measure.pi (fun v => muNl C (X.pl v) v) A = Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' A) := by
  intro D X θ C A hθ _hA
  have hsf : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muNv C v) := by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ w rfl
      exact sf_muNl C τ hθ
    intro v
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  obtain ⟨hemb, hmap⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C hsf hθ
  have h := congrArg (fun μ => μ (Formalism.L2.SG.LoopTerm.trInf C '' A)) hmap
  rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective] at h
  exact h

end GlobalTheory
