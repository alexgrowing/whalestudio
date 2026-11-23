import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftSpacesOverDefiniteForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_spaces_over_definite_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (m : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G) (s : D.what₂.Tup → ℕ → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tL : ∀ μ j, Tie1 D.what₂.embLL (m μ j) (s μ j)) (hL : ∀ (i : Fin D.R.m) t, m (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t), ∃ l : LfD D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) D.what₂.Tup Φ fun μ j => (s μ j).A, Nonempty (LfT y F.lv2 rep (Mt := fun μ j => (s μ j).A) (fun i t x => ((tL (y.tup t) ((i : ℕ) + 1)).cast (hL i t)).j x) l) := by
  first | exact @GlobalTheory.LiftSpaces.exists_lift_spaces | exact GlobalTheory.LiftSpaces.exists_lift_spaces | (intros; apply GlobalTheory.LiftSpaces.exists_lift_spaces <;> assumption)
