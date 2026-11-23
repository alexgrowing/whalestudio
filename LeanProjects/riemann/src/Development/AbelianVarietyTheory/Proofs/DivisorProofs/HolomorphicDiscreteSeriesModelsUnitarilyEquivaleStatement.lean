import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDiscreteSeriesModelsUnitarilyEquivale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_discrete_series_models_unitarily_equivalent : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M M' : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec) (v' : M'.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → IsExtVec M' v' → ∃ U : ∀ τ, M'.H τ ≃ₗᵢ[ℂ] M.H τ, ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, U τ (M'.rep τ g y) = M.rep τ g (U τ y) := by
  first | exact @GlobalTheory.HolDict.holModel_unique | exact GlobalTheory.HolDict.holModel_unique | (intros; apply GlobalTheory.HolDict.holModel_unique <;> assumption)
