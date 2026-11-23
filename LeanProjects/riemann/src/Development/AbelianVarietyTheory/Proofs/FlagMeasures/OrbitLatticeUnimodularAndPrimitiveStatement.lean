import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_lattice_unimodular_and_primitive : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ ∈ Y.what₂ u, Submodule.IsLattice D.host.E (GlobalTheory.RowsOrb.Lmap X u Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) (GlobalTheory.RowsOrb.Lmap X u Λ) ∧ ∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ GlobalTheory.RowsOrb.Lmap X u Λ ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  first | exact @GlobalTheory.RowsOrb.Basic.lmap_basic | exact GlobalTheory.RowsOrb.Basic.lmap_basic | (intros; apply GlobalTheory.RowsOrb.Basic.lmap_basic <;> assumption)
