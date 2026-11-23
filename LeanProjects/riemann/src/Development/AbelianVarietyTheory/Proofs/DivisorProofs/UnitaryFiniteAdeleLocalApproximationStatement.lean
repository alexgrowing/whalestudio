import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFiniteAdeleLocalApproximation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_finite_adele_local_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : ℕ) (W : Spc F E d) (hf : UA σ W.J), ∃ h : Pl F → UA σ W.J, ∀ v, h v ∈ UAt σ W (evFin F v) ∧
      ∀ u : AF F, At (evFin F v) u → u • mat (h v) = u • mat hf := by
  first | exact @GlobalTheory.AdelicLocalPoint.localComponents | exact GlobalTheory.AdelicLocalPoint.localComponents | (intros; apply GlobalTheory.AdelicLocalPoint.localComponents <;> assumption)
