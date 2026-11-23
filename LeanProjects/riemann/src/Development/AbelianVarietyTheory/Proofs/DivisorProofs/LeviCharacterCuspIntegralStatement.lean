import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCharacterCuspIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarFundamentalDomainExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_character_cusp_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (α β : Chr F E) (za zb : ℝ),
    (∃ K : Set (unip σ W H), IsCompact K ∧ ∀ u : unip σ W H, ∃ γ ∈ (ratU σ W.J).subgroupOf (unip σ W H), γ * u ∈ K) →
    ∀ (t₀ : (AE F E)ˣ) (m₀ : UA σ W.J), IsLevi (W₁ := W₁) H t₀ 1 m₀ →
    (α t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ za : ℝ) : ℂ) ≠ (β t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ zb : ℝ) : ℂ) →
    ∃ (D : Submodule ℂ (UA σ W.J → ℂ)) (Λ : (UA σ W.J → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ)),
      (∀ f fa fb : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ z, f (γ * z) = f z) →
        SplitZ W₁ H α β za zb f fa fb → f ∈ D ∧ Λ f = fa) ∧
      (∀ f ∈ D, ∀ y : UA σ W.J, (fun z => f (z * y)) ∈ D ∧ Λ (fun z => f (z * y)) = fun z => Λ f (z * y)) ∧
      ∀ f ∈ D, HasLaw W₁ H α za (Λ f) ∧ ∀ u ∈ unip σ W H, ∀ z, Λ f (u * z) = Λ f z := by
  first | exact @GlobalTheory.CTFirst.ct_first_linear | exact GlobalTheory.CTFirst.ct_first_linear | (intros; apply GlobalTheory.CTFirst.ct_first_linear <;> assumption)
