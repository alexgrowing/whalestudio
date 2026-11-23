import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F)), 1 ≤ M → IsHermND σ J → μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ fib : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E), IsFibreFamily μ (fun X => qR (Ainf F) σ J (X 0)) id Set.univ ν {c : Ainf F | ∀ w, c w ≠ 0} fib := by
  first | exact @GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf | exact GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf | (intros; apply GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf <;> assumption)
