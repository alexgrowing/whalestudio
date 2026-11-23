import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_type_dimension_and_local_integrals_degree_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P → ∀ (δ : (P.adicCompletion L)ˣ →* ℂˣ) (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → (∀ i, IsNu P (ν i)) → ∀ r t j : ℕ, 1 ≤ t → (∃ n, TypeDimAt P δ ν r t j n) ∧ ∃ z, StepAt P δ ν r t j z := by
  first | exact @GlobalTheory.TypeStep.exists_typeDim_step | exact GlobalTheory.TypeStep.exists_typeDim_step | (intros; apply GlobalTheory.TypeStep.exists_typeDim_step <;> assumption)
