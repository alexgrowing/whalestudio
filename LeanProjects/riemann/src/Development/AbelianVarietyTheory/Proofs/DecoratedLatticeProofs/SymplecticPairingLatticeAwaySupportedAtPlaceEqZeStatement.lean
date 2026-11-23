import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticPairingLatticeAwaySupportedAtPlaceEqZe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticPairing_latticeAway_supportedAt_place_eq_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop), ¬ P p.v → ∀ u ∈ latO S T MS MT P, ∀ x : WO S T, (∀ i j, (p.e + cA D p.e) * x i j = x i j) → symplO S T u x = 0 := by
  first | exact @GlobalTheory.FinPl.OffSympl.symplO_off_eq_zero | exact GlobalTheory.FinPl.OffSympl.symplO_off_eq_zero | (intros; apply GlobalTheory.FinPl.OffSympl.symplO_off_eq_zero <;> assumption)
