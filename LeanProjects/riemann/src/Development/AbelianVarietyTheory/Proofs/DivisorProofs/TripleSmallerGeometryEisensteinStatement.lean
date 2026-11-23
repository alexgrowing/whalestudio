import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleSmallerGeometryEisenstein
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_smaller_geometry_eisenstein : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → ∀ eb : Fn F a (a + b) →ₗ[ℂ] Fn F n₁ (a + b), IsEv B G₁.M M₂ H₀.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H₀.x) z} eb → ∀ (t : (AE F E)ˣ) (m₀ : UA σ G₁.V.J), IsLevi (W₁ := X₁) H₀ t 1 m₀ → ∀ Φ ∈ schA F (Fin a × Fin (a + b)), eb (om₁ (m₀, 1) Φ) = (((X.β / X.α) t : ℂ) * (((absE F E t : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • eb Φ := by
  first | exact @GlobalTheory.ThK.evalLine_leviV | exact GlobalTheory.ThK.evalLine_leviV | (intros; apply GlobalTheory.ThK.evalLine_leviV <;> assumption)
