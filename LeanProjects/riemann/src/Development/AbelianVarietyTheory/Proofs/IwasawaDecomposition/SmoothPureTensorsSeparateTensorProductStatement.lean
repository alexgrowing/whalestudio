import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothPureTensorsSeparateTensorProduct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothPureTensors_separate_tensorProduct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (x : SmT M), x ≠ 0 → ∃ w : M.Vec, ellT M (fun τ => (w τ : M.H τ)) (inclT M x) ≠ 0 := by
  first | exact @GlobalTheory.Mem.PureSep.exists_ellT_ne_zero | exact GlobalTheory.Mem.PureSep.exists_ellT_ne_zero | (intros; apply GlobalTheory.Mem.PureSep.exists_ellT_ne_zero <;> assumption)
