import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisGramLocalForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitHomVal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_basis_gram_local_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n m : ℕ) (W : Spc F E n) (W₁ : Spc F E m) (H : Plane E n m) (i₀ i₁ : ℕ), (∀ x, σ (σ x) = x) → H.IsAdapted σ B W W₁ i₀ i₁ →
    (∀ i j, σ (W.J j i) = -W.J i j) → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (e : GlobalTheory.SplitCoord.Ix m ≃ Fin n),
    ((GlobalTheory.SplitCoord.basMat H e).map t)ᵀ * W.J.map t * (GlobalTheory.SplitCoord.basMat H e).map (t.comp σ) =
      GlobalTheory.SplitCoord.gam e (W₁.J.map t) := by
  first | exact @GlobalTheory.SplitCoord.basMat_gram | exact GlobalTheory.SplitCoord.basMat_gram | (intros; apply GlobalTheory.SplitCoord.basMat_gram <;> assumption)
