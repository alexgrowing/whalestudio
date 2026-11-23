import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelConstant_exponents_finite : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀), k.YFinite := by
  first | exact @GlobalTheory.ExponentsFinite.yFinite | exact GlobalTheory.ExponentsFinite.yFinite | (intros; apply GlobalTheory.ExponentsFinite.yFinite <;> assumption)
