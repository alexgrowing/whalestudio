import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasisGramEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_basis_gram_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ i j : Ix m, form σ W.J (fun r => basP H r i) (fun r => basP H r j) = gI W₁.J i j := by
  first | exact @GlobalTheory.QhtUnip.form_adaptedBasis_eq_gram | exact GlobalTheory.QhtUnip.form_adaptedBasis_eq_gram | (intros; apply GlobalTheory.QhtUnip.form_adaptedBasis_eq_gram <;> assumption)
