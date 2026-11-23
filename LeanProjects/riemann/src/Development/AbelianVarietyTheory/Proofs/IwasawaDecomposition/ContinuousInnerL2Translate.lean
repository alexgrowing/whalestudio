import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem continuous_inner_l2_translate :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ u ∈ smSub G (trRep σ P), ∀ f : Lp ℂ 2 ν, Continuous fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act hact a A ha _ hA u hu f
  obtain ⟨hc, ⟨C, hC⟩, heq⟩ := ha u hu
  have hfi : Integrable (f : X → ℂ) ν := (Lp.memLp f).integrable (by norm_num)
  have key : (fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ)
      = fun g => ∫ x, ⟪f x, a u (act g x)⟫_ℂ ∂ν := by
    funext g
    rw [L2.inner_def]
    have hm : σ (umat g) u ∈ smSub G (trRep σ P) := by
      exact sigma_mem hP hG hσ hu g.2
    refine integral_congr_ae ?_
    filter_upwards [hA _ hm] with x hx
    rw [hx, heq]
  rw [key]
  refine continuous_of_dominated (bound := fun x => ‖f x‖ * C) ?_ ?_ (hfi.norm.mul_const C) ?_
  · intro g
    refine AEStronglyMeasurable.inner hfi.aestronglyMeasurable ?_
    exact (hc.comp (hact.comp (Continuous.prodMk_right g))).aestronglyMeasurable
  · intro g
    refine Eventually.of_forall fun x => ?_
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  · refine Eventually.of_forall fun x => ?_
    exact continuous_const.inner (hc.comp (hact.comp (Continuous.prodMk_left x)))

end GlobalTheory.SmVec
