import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semicharacter_completedSelfDualLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), l.map (infPart D) = 0) ∧ ∃ χ : WO S T → ℂ, (∀ x, (¬ ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - l).map (finPart D) = 0) → χ x = 0) ∧ (∀ x, ‖χ x‖ ≤ 1) ∧ χ 0 = 1 ∧ (∀ x y, y.map (finPart D) = 0 → χ (x + y) = χ x) ∧ (∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ x, ψ (symplOH S T x (2 • u)) * χ (x + 2 • u) = χ x) ∧ ∀ e, IsSplitIdem D e → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e u → ∀ x, ψ (symplOH S T x u) * χ (x + u) = χ x := by
  first | exact @GlobalTheory.SemiChar.exists_semichar | exact GlobalTheory.SemiChar.exists_semichar | (intros; apply GlobalTheory.SemiChar.exists_semichar <;> assumption)
