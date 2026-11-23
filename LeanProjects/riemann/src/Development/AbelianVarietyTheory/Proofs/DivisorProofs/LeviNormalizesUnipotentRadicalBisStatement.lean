import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalBis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_radical_bis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ levi σ J X Y {0}, ∀ u ∈ unipRad σ J (col X), m * u * m⁻¹ ∈ unipRad σ J (col X)) ∧ (∀ g ∈ unipRad σ J (col X), g ∈ levi σ J X Y {0} → g = 1) ∧ (∀ γ ∈ ratPts σ J, γ ∈ levi σ J X Y {0} → γ ∈ leviOne σ J X Y {0}) ∧ (∀ u ∈ unipRad σ J (col X), Scales σ J (col X) u 1) ∧ (∀ m ∈ leviOne σ J X Y {0}, ∃ l, Scales σ J (col X) m l ∧ absE F E l = 1) ∧ ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (col X) γ l → absE F E l = 1 := by
  first | exact @GlobalTheory.ResLine.LeviFacts.levi_facts | exact GlobalTheory.ResLine.LeviFacts.levi_facts | (intros; apply GlobalTheory.ResLine.LeviFacts.levi_facts <;> assumption)
