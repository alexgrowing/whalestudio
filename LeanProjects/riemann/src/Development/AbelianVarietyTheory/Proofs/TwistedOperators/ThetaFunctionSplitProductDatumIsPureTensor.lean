import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivRealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleMulSingle
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (ι : Type) (s : Finset ι) (v : ι → FinPl D) (a : ι → AE D), (∀ i ∈ s, IsSplitIdem D (a i) ∧ a i + cA D (a i) = idem D (.inl (v i))) → Set.InjOn v s → ∀ Φ : ι → WO S T → ℂ, (∀ i ∈ s, IsSBHalf (a i) (latO S T ΛS ΛT fun _ => True) (Φ i)) → ∀ (x : Place D → WO S T → ℂ) (f Ψ : WO S T → ℂ), (∀ i ∈ s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i) (x (.inl (v i)))) → (∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → x p = f₀) → (∀ t, IsHalf (∑ i ∈ s, a i) t → Ψ t = ∏ i ∈ s, Φ i (a i • t)) → (∀ t, ¬ IsHalf (∑ i ∈ s, a i) t → Ψ t = 0) → IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i ∈ s, a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ Ψ f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  exact GlobalTheory.PlaceTensor.SplitProduct.isPure_of_facts D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕
    (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1
    (GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ)
    (GlobalTheory.T.pureTensor_linear_in_factor_and_heisenbergDeriv_real D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1
    (fun a h1 h2 h3 =>
      ⟨fun x y hx hy Tm hTm =>
        ((GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates D ψ S T ΛS ΛT (base_std hB) hB.2.2.1 hB.2.2.2.1 a h1 h2 h3).1 x y hx hy).2 f₀ Tm hTm,
        (GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates D ψ S T ΛS ΛT (base_std hB) hB.2.2.1 hB.2.2.2.1 a h1 h2 h3).2⟩)
