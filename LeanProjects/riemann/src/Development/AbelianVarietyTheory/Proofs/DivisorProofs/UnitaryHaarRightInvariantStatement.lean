import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHaarRightInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_haar_right_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ μ : Measure (UA σ X.J), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.HermUnimod.isMulRightInvariant_of_isHerm | exact GlobalTheory.HermUnimod.isMulRightInvariant_of_isHerm | (intros; apply GlobalTheory.HermUnimod.isMulRightInvariant_of_isHerm <;> assumption)
