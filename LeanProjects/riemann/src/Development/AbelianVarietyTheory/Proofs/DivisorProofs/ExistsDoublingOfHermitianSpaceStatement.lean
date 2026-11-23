import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoublingOfHermitianSpace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubling_of_hermitian_space : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n r s' : ℕ) (X : Spc F E n), X.IsHerm σ B r s' →
    ∃ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ := by
  first | exact @GlobalTheory.HermDouble.exists_isDbl | exact GlobalTheory.HermDouble.exists_isDbl | (intros; apply GlobalTheory.HermDouble.exists_isDbl <;> assumption)
