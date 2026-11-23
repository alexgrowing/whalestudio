import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalElements
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_finite_generation_vector : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n r s : ℕ) (X : Spc F E n), X.IsHerm σ B r s →
    ∀ K : Subgroup (UA σ X.J), IsStab B K →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : UA σ X.J →* Module.End ℂ V) (x : V) (S : Submodule ℂ V), FiniteDimensional ℂ S →
    (∀ k ∈ KInf σ X B.emb, ρ k x ∈ S) → ∀ U : Subgroup (UA σ X.J), IsOpen (U : Set (UA σ X.J)) →
    (∀ k ∈ U, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → ρ k x = x) →
    FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ k ∈ K, y = ρ k x}) := by
  first | exact @GlobalTheory.KFinStab.span_finiteDimensional | exact GlobalTheory.KFinStab.span_finiteDimensional | (intros; apply GlobalTheory.KFinStab.span_finiteDimensional <;> assumption)
