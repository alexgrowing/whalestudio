import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerHaarQuotientSecond
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_stabilizer_haar_quotient_second : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ μ : Measure (stabAt σ G.V (evFin F v) H.x), μ.IsHaarMeasure →
    ∀ q : stabAt σ G.V (evFin F v) H.x, (∃ g₀ : UA σ G₁.V.J, IsLevi H 1 g₀ q.1.1 ∧ g₀ ∈ UAt σ G₁.V (evFin F v)) →
      Measure.map (· * q) μ = μ := by
  first | exact @GlobalTheory.ThK.LemF.LeviInv.levi_map_mul_right | exact GlobalTheory.ThK.LemF.LeviInv.levi_map_mul_right | (intros; apply GlobalTheory.ThK.LemF.LeviInv.levi_map_mul_right <;> assumption)
