import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalContinuous
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_local_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ m₀ : idelesAt E (evFin F v) →* UAtSub σ G.V (evFin F v), (∀ t, IsLevi H t.1 (1 : UA σ G₁.V.J) (m₀ t).1) →
    ∀ hn : (∀ t, ∀ q ∈ stabAt σ G.V (evFin F v) H.x, (m₀ t)⁻¹ * q * m₀ t ∈ stabAt σ G.V (evFin F v) H.x),
    ∀ μ : Measure (stabAt σ G.V (evFin F v) H.x), μ.IsHaarMeasure → ∀ t,
      μ.map (fun q : stabAt σ G.V (evFin F v) H.x => (⟨(m₀ t)⁻¹ * q * m₀ t, hn t q q.2⟩ : stabAt σ G.V (evFin F v) H.x)) = absPow E (evFin F v) (b + 1) t • μ := by
  first | exact @GlobalTheory.ThK.LemF.QuotInv.modulus_levi | exact GlobalTheory.ThK.LemF.QuotInv.modulus_levi | (intros; apply GlobalTheory.ThK.LemF.QuotInv.modulus_levi <;> assumption)
