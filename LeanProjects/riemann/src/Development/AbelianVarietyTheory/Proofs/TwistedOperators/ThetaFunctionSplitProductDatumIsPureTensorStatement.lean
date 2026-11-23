import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionSplitProductDatumIsPureTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_splitProductDatum_isPureTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (ι : Type) (s : Finset ι) (v : ι → FinPl D) (a : ι → AE D), (∀ i ∈ s, IsSplitIdem D (a i) ∧ a i + cA D (a i) = idem D (.inl (v i))) → Set.InjOn v s → ∀ Φ : ι → WO S T → ℂ, (∀ i ∈ s, IsSBHalf (a i) (latO S T ΛS ΛT fun _ => True) (Φ i)) → ∀ (x : Place D → WO S T → ℂ) (f Ψ : WO S T → ℂ), (∀ i ∈ s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i) (x (.inl (v i)))) → (∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → x p = f₀) → (∀ t, IsHalf (∑ i ∈ s, a i) t → Ψ t = ∏ i ∈ s, Φ i (a i • t)) → (∀ t, ¬ IsHalf (∑ i ∈ s, a i) t → Ψ t = 0) → IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i ∈ s, a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ Ψ f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  first | exact @GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure | exact GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure | (intros; apply GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure <;> assumption)
