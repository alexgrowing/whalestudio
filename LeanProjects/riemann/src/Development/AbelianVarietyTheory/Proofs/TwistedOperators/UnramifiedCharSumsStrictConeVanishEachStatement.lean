import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedCharSumsStrictConeVanishEach
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.ExistsStrictAnti
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_char_sums_strict_cone_vanish_each : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r n : ℕ) (E : Fin n → Multiset ((Fin r → kˣ) →* ℂˣ)) (c : Fin n → ℂ), (∀ i, ∀ χ ∈ E i, ∀ t ∈ torusO k (Fin r), χ t = 1) → (∀ t ∈ IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.strictCone ϖ r, ∑ i, c i * IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum (E i) t = 0) → ∀ [DecidableEq ((Fin r → kˣ) →* ℂˣ)] (χ : (Fin r → kˣ) →* ℂˣ), ∑ i, c i * ((E i).count χ : ℂ) = 0 := by
  first | exact @GlobalTheory.ConeCount.sum_count_eq_zero | exact GlobalTheory.ConeCount.sum_count_eq_zero | (intros; apply GlobalTheory.ConeCount.sum_count_eq_zero <;> assumption)
