import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroGaussianVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_gaussian_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.ActsLaws →
    ∃ f₀ : SInf F (Fin n × Fin d), f₀ ≠ 0 ∧ M.IsGauss B.ψ B.emb f₀ := by
  first | exact @GlobalTheory.FockVacuum.exists_ne_zero_isGauss | exact GlobalTheory.FockVacuum.exists_ne_zero_isGauss | (intros; apply GlobalTheory.FockVacuum.exists_ne_zero_isGauss <;> assumption)
