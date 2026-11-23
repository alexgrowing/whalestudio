import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFrameLevi_normalizes_radical_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, ∀ u ∈ unipRad σ J X, m * u * m⁻¹ ∈ unipRad σ J X) ∧ (∀ g ∈ unipRad σ J X, g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} → g = 1) ∧ (∀ u ∈ unipRad σ J X, ScalesBy σ J X u 1) ∧ (∀ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ β, ScalesBy σ J X m β ∧ absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ (∀ γ ∈ ratPts σ J, ∀ β, ScalesBy σ J X γ β → absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} ∧ IsClosed ((GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  first | exact @GlobalTheory.ResidueEisenstein.frame_levi_facts | exact GlobalTheory.ResidueEisenstein.frame_levi_facts | (intros; apply GlobalTheory.ResidueEisenstein.frame_levi_facts <;> assumption)
