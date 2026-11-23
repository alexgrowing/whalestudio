import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockActionsIsHolomorphicProductKRepFamily
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockActions_isHolomorphicProductKRepFamily : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), IsHolFam ε fockL (factK n ε x₁ x₂ x₃) ∧ IsHolFam (fun _ => allPos n) fockL (factU (n := n) ε x₁ x₂ x₃) := by
  first | exact @GlobalTheory.FockHol.main | exact GlobalTheory.FockHol.main | (intros; apply GlobalTheory.FockHol.main <;> assumption)
