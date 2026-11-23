import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualC_hyperbolicExtensionLattice_conjStable : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (ρ : ℕ) (e f : Fin ρ → Y.V), GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsDec Y X ι (fun _ : Fin 1 => z) (-GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.Tu D u) e f → ∀ L, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSDIn Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.flatSp Y X ι z) L → ∀ nn, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable nn → Formalism.IndefR.Datum.IsSelfDualC Y (Formalism.L2.Herm.crdLat Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.lamN Y e f L nn)) := by
  first | exact @GlobalTheory.HypLattice.isSelfDualC_lamN | exact GlobalTheory.HypLattice.isSelfDualC_lamN | (intros; apply GlobalTheory.HypLattice.isSelfDualC_lamN <;> assumption)
