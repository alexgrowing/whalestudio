import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorCommutesIsometry
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_commutes_isometry : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ → ∀ (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ), φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V → gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) := by
  first | exact @GlobalTheory.Mem.Isom.IsoMat.gelf_tr | exact GlobalTheory.Mem.Isom.IsoMat.gelf_tr | (intros; apply GlobalTheory.Mem.Isom.IsoMat.gelf_tr <;> assumption)
