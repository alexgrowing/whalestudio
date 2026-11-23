import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingMultiplicative
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_multiplicative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁), B.IsGood σ → X.IsHerm σ B r s →
    X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    (∀ l l' g g', m (l * l') (g * g') = m l g * m l' g') ∧ Continuous (fun x : (AE F E)ˣ × UA σ X₁.J => m x.1 x.2) ∧
    (∀ l g, m l g ∈ GlobalTheory.IwLine.lineStab σ X.J H.x) ∧
    (∀ q ∈ GlobalTheory.IwLine.lineStab σ X.J H.x, ∃! z : unip σ X H × ((AE F E)ˣ × UA σ X₁.J), q = z.1.1 * m z.2.1 z.2.2) ∧
    IsClosed (GlobalTheory.IwLine.lineStab σ X.J H.x : Set (UA σ X.J)) ∧ IsClosed (unip σ X H : Set (UA σ X.J)) ∧
    unip σ X H ≤ GlobalTheory.IwLine.lineStab σ X.J H.x ∧ ∀ q ∈ GlobalTheory.IwLine.lineStab σ X.J H.x, ∀ u ∈ unip σ X H, q * u * q⁻¹ ∈ unip σ X H := by
  first | exact @GlobalTheory.LeviSec.leviSection_props | exact GlobalTheory.LeviSec.leviSection_props | (intros; apply GlobalTheory.LeviSec.leviSection_props <;> assumption)
