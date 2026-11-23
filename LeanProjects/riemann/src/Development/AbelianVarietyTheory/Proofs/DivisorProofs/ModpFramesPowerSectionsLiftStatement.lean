import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPowerSectionsLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modp_frames_power_sections_lift : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) (ι : Type) (N : ℕ) (U : ι → X.Opens)
    (M : ι → Matrix (Fin N) (Fin N) X.functionField) (c : ι → Fin N → X.functionFieldˣ), GlobalTheory.FrameGlue.ModPFrames p U M c →
    ∀ (L : Fin N → LB X) (hL : ∀ i, (L i).IsLB) (m : ℕ), (∀ i, GlobalTheory.FrameGlue.PowOfFrames p U (fun a => c a i) m (L i)) →
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (ι' : Z ⟶ X), (p : Γ(Z, ⊤)) = 0 →
      ∃ g : Fin N → Pic Z, FlagOfTriv g ∧ ∀ i, CechPic.pull ι' (cls (L i) (hL i)) = m • g i := by
  first | exact @GlobalTheory.FrameGlue.flagOfTriv_of_modPFrames | exact GlobalTheory.FrameGlue.flagOfTriv_of_modPFrames | (intros; apply GlobalTheory.FrameGlue.flagOfTriv_of_modPFrames <;> assumption)
