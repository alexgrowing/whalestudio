import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlockDiagReductionToFlagGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_blockDiag_reduction_to_flagGroup : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (g : G), (∀ PP' : R.Pg, PP' ≠ ⟨PP, hPP⟩ → R.eG g PP' = 1) → ∀ κ : GA D (Vc D i), κ ∈ GfC (Vc D i) → finE (Vc D i) κ ∈ Formalism.L2.DIV.St (R.βV i) → ((redFn (R.βV i) PP (finE (Vc D i) κ) : GL (Fin (Vc D i).rank) (kP PP)) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) = (Matrix.fromBlocks ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (kP PP))).submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm → (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) → IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ = 1 := by
  first | exact @GlobalTheory.LiftDiag.lift_diag | exact GlobalTheory.LiftDiag.lift_diag | (intros; apply GlobalTheory.LiftDiag.lift_diag <;> assumption)
