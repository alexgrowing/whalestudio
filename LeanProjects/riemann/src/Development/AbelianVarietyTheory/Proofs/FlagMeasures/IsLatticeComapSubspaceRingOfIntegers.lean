import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Imports
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubtype
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_ne_zero_smul_mem_of_span_eq_top {K V : Type} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.TargetStatementBis.target
  | exact _root_.GlobalTheory.TargetStatementBis.target
  | (apply _root_.GlobalTheory.TargetStatementBis.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementBis.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementBis.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementBis.target ..)

theorem isLattice_comap_subtype_ringOfIntegers {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  first
  | exact @_root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype
  | exact _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype
  | (apply _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype ..)

end GlobalTheory
