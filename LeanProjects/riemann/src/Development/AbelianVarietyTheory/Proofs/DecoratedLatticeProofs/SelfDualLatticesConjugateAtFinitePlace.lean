import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.FinPl.SelfDualConj

theorem conj_at_place : ∀ (D : D7) (V : HSp D) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M →
    ∀ x : Pl D, ∃ g ∈ grpAt V (· = x), Moves V g L M (· = x) := by
  intro D V L M hL hM x
  obtain ⟨γ, hγ, h⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D V x (latV V L (· = x)) (latV V M (· = x)) (GlobalTheory.FinPl.TamePlaces.tame D x)
    (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V L x hL) (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V M x hM)
  exact ⟨γ, hγ, fun y hy => h y hy⟩

end GlobalTheory.FinPl.SelfDualConj
