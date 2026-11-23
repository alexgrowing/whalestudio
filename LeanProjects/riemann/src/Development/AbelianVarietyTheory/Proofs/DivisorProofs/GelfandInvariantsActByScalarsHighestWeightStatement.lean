import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsActByScalarsHighestWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_invariants_act_by_scalars_highest_weight : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n) (w : Fin n → ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), OrthFr Hm q x₀ → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ → ∀ v₀, v₀ ≠ 0 → SmoothVec (lieH Hm) σ v₀ → (∀ a c : Fin n, a ≤ c → dRepC Hm σ (x₀ * Matrix.single a c 1 * x₀⁻¹) v₀ = if a = c then (w a : ℂ) • v₀ else 0) → ∀ k, ∃ c : ℂ, ∀ v, SmoothVec (lieH Hm) σ v → gelfRep Hm σ k v = c • v := by
  first | exact @GlobalTheory.HolDict.GelfScalar.gelfRep_scalar | exact GlobalTheory.HolDict.GelfScalar.gelfRep_scalar | (intros; apply GlobalTheory.HolDict.GelfScalar.gelfRep_scalar <;> assumption)
