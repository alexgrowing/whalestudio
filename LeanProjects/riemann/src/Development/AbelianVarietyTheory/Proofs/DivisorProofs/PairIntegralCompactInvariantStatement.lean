import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntegralCompactInvariant
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
theorem _root_.GlobalTheory.T.pair_integral_compact_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (T : Finset (Pl F)) (k : UA σ W.J), k ∈ UAt σ W (fun u : AF F => u.2) →
    (∀ v ∈ T, ∀ u : AF F, At (evFin F v) u → u • mat k = u • (1 : Matrix (Fin d) (Fin d) (AE F E))) →
    (∀ v ∉ T, ∀ g ∈ UAt σ W (evFin F v), (∀ u : AF F, At (evFin F v) u → u • mat g = u • mat k) →
      Acts (evFin F v) (om (1, g)) (M.vac v) (M.vac v)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ v ∉ T, φ v = M.vac v) → om (1, k) (pure f φ) = pure f φ := by
  first | exact @GlobalTheory.TailFix.fix_pure | exact GlobalTheory.TailFix.fix_pure | (intros; apply GlobalTheory.TailFix.fix_pure <;> assumption)
