import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjective
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → (∀ f, IsHol θ S T ψ f → Differentiable ℂ (xiN θ S T hS hT δ sc f)) ∧ ∀ f, IsThetaFunO ψ S T f → xiN θ S T hS hT δ sc f = 0 → f = 0 := by
  first | exact @GlobalTheory.AdForm.VacRead.xiN_entire_and_injective | exact GlobalTheory.AdForm.VacRead.xiN_entire_and_injective | (intros; apply GlobalTheory.AdForm.VacRead.xiN_entire_and_injective <;> assumption)
