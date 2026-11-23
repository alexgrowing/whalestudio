import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHeisenbergTranslateExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_heisenberg_translate_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ w₀ : Fin m → E, ∃ γ ∈ ratU σ W.J, ∃ (a : Fin m → AE F E) (α : AE F E),
      crd H γ = Heisenberg₂ a (fun k => inclR (F := F) (AF F) (w₀ k)) α := by
  first | exact @GlobalTheory.LiftHeisW.exists_ratU_heis | exact GlobalTheory.LiftHeisW.exists_ratU_heis | (intros; apply GlobalTheory.LiftHeisW.exists_ratU_heis <;> assumption)
