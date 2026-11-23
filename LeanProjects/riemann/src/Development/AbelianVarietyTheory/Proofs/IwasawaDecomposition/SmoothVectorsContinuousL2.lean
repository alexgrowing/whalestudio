import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem continuous_toL2_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ φ, IsTest φ → Continuous fun w => A (gard ε σ φ w) := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act _ a A _ hs hA φ hφ
  let g := GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφ.2
  have hg : ∀ w, gard ε σ φ w = g w := fun w => gard_eq hσ hφ w
  let L : H →ₗ[ℂ] Lp ℂ 2 ν := A.comp (g : H →ₗ[ℂ] H)
  have hL : ∀ w, L w = A (gard ε σ φ w) := fun w => rfl
  have hc : ∀ x, Continuous fun w => a (gard ε σ φ w) x := fun x => by
    obtain ⟨C, hC⟩ := (GlobalTheory.T.sobolevContinuous_form_gardingVector n ε H σ P G hP hG hσ _ (hs x)).1 φ hφ
    exact (LinearMap.mkContinuous (((LinearMap.proj x).comp a).comp (g : H →ₗ[ℂ] H)) C hC).continuous
  have key : Continuous L := by
    refine L.continuous_of_seq_closed_graph fun u w f hu hf => ?_
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
    have h1 : ∀ᵐ x ∂ν, ∀ k, (L (u k) : X → ℂ) x = a (gard ε σ φ (u k)) x :=
      ae_all_iff.2 fun k => hA _ (gard_mem hP hG hσ hφ (u k))
    refine Lp.ext ?_
    filter_upwards [hae, h1, hA _ (gard_mem hP hG hσ hφ w)] with x hx h1x h2x
    have h3 : Tendsto (fun k => a (gard ε σ φ (u (ns k))) x) atTop (𝓝 (a (gard ε σ φ w) x)) :=
      ((hc x).tendsto w).comp (hu.comp hns.tendsto_atTop)
    have h4 : Tendsto (fun k => a (gard ε σ φ (u (ns k))) x) atTop (𝓝 (f x)) :=
      hx.congr fun k => h1x (ns k)
    exact (tendsto_nhds_unique h4 h3).trans h2x.symm
  exact key

end GlobalTheory.SmVec
