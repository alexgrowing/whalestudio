import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyMemMaximalCompact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_mem_maximal_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d), W.L.IsLattice E → ∀ hf : UA σ W.J,
    ∀ᶠ v in Filter.cofinite, ∀ g ∈ UAt σ W (evFin F v), (∀ u : AF F, At (evFin F v) u → u • mat g = u • mat hf) →
      g ∈ GlobalTheory.InertSph.KAt σ W v := by
  first | exact @GlobalTheory.IntegralAE.eventually_mem_KAt | exact GlobalTheory.IntegralAE.eventually_mem_KAt | (intros; apply GlobalTheory.IntegralAE.eventually_mem_KAt <;> assumption)
