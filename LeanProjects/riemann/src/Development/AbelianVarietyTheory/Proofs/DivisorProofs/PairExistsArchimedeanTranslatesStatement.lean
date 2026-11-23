import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairExistsArchimedeanTranslates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_exists_archimedean_translates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (ε : InfinitePlace F → ℤˣ) (α : Fin n × Fin d → mixedEmbedding.mixedSpace F),
    ∃ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w, u'.map (piInf (B.emb w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) ∧
      (∀ i, evI F ((M.co.e u).1 i) = 0) ∧ ∀ i, evI F ((M.co.e u').1 i) = α i := by
  first | exact @GlobalTheory.FockTransv.transversal | exact GlobalTheory.FockTransv.transversal | (intros; apply GlobalTheory.FockTransv.transversal <;> assumption)
