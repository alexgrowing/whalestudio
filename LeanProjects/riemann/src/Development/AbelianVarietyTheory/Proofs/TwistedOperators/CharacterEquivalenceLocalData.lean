import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.ChrTie

theorem unrAt_iff_and_val_eq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (UnrAt c w ↔ χ.UnrAt w) ∧ val c w = χ.val w :=
  fun _ _ _ h w => ⟨GlobalTheory.LFun.unrAt_iff_of_chrEq h w, GlobalTheory.LFun.val_eq_of_chrEq h w⟩

end GlobalTheory.ChrTie
