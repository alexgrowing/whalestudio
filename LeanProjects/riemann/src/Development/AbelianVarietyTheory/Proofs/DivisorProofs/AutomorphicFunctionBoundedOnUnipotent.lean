import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoundedHeightReductionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.UnipBound

set_option synthInstance.maxHeartbeats 400000 in

theorem bounded_on_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ f : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) → ∀ h, ∃ C : ℝ, ∀ u ∈ unip σ W H', ‖f (u * h)‖ ≤ C := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s hB hW hH' f hf hinv h
  obtain ⟨R, hR⟩ := GlobalTheory.T.unipotent_bounded_height_reduction F E σ B d d₁ W W₁ H' i₀ i₁ r s hB hW hH'
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e₀⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e₀.isEmbedding.t2Space
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F W.J) : Set (GL (Fin d) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin d) (AE F E) => (g : Matrix (Fin d) (Fin d) (AE F E)) := Units.continuous_val
    exact isClosed_eq (((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA))) continuous_const
  have hK : IsCompact {g : UA σ W.J | ht g ≤ R} :=
    hc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_heightGL_le F R)
  have hcont : Continuous fun g : UA σ W.J => f (g * h) := hf.comp (continuous_id.mul continuous_const)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun u hu => ?_⟩
  obtain ⟨γ, hγ, hγR⟩ := hR u hu
  have e : f (u * h) = f ((γ * u) * h) := by rw [mul_assoc, hinv γ hγ.1]
  rw [e]
  exact hC (γ * u) hγR

end GlobalTheory.ThK.UnipBound

end
