import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionUnipotentLevi
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_unipotent_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    ∀ g : UA σ G.W.J, ∃ n ∈ unip σ G.W H', ∃ (t : (AE F E)ˣ) (m₁ : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m₁ ∧
      ∃ (h₁ : UA σ W₁.J) (m₂ : UA σ G.W.J), IsLevi (W₁ := W₁) H' 1 h₁ m₂ ∧ ∃ k ∈ finK σ G.W B.emb, g = n * m₁ * m₂ * k := by
  first | exact @GlobalTheory.ThK.IwasawaLine.iwasawa | exact GlobalTheory.ThK.IwasawaLine.iwasawa | (intros; apply GlobalTheory.ThK.IwasawaLine.iwasawa <;> assumption)
