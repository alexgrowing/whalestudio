import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem inner_l2_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ φ, IsTest φ → ∀ w ∈ smSub G (trRep σ P), ∀ f : Lp ℂ 2 ν, ⟪f, A (gard ε σ φ w)⟫_ℂ = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪f, A (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act hact a A ha hsob hA φ hφ w hw f
  have hemb := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Formalism.REAL.UJ ε) := hemb.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Formalism.REAL.UJ ε) := hemb.locallyCompactSpace
  haveI : SigmaFinite (Formalism.REAL.muG ε) := inferInstance
  obtain ⟨hc, ⟨C, hC⟩, hact'⟩ := ha w hw
  have key : ∀ v ∈ smSub G (trRep σ P), ⟪f, A v⟫_ℂ = ∫ x, ⟪f x, a v x⟫_ℂ ∂ν := fun v hv => by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hA v hv] with x hx
    rw [hx]
  have h1 : ∀ x, a (gard ε σ φ w) x = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • a w (act g x) ∂(Formalism.REAL.muG ε) := fun x => by
    have := ((GlobalTheory.T.sobolevContinuous_form_gardingVector n ε H σ P G hP hG hσ _ (hsob x)).2 w hw).2 φ hφ
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, hact'] at this
    exact this
  have hφi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) (Formalism.REAL.muG ε) := by
    simpa using hφ.integrable (ε := ε) (F := fun _ => (1 : ℝ)) continuous_const
  have hf1 : Integrable (f : X → ℂ) ν := (Lp.memLp f).integrable (by norm_num)
  have hint : Integrable (fun p : Formalism.REAL.UJ ε × X => φ (umat p.1) • ⟪f p.2, a w (act p.1 p.2)⟫_ℂ)
      ((Formalism.REAL.muG ε).prod ν) := by
    refine Integrable.mono' ((hφi.norm.mul_prod hf1.norm).mul_const C) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.smul hφi.aestronglyMeasurable.comp_fst ?_
      exact AEStronglyMeasurable.inner hf1.aestronglyMeasurable.comp_snd (hc.comp hact).aestronglyMeasurable
    · rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))) (norm_nonneg _)
  rw [key _ (gard_mem hP hG hσ hφ w)]
  calc ∫ x, ⟪f x, a (gard ε σ φ w) x⟫_ℂ ∂ν
      = ∫ x, ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪f x, a w (act g x)⟫_ℂ ∂(Formalism.REAL.muG ε) ∂ν := by
        congr 1
        funext x
        have hcx : Continuous fun g : Formalism.REAL.UJ ε => a w (act g x) :=
          hc.comp (hact.comp (Continuous.prodMk_left x))
        rw [h1, ← integral_inner (hφ.integrable hcx)]
        congr 1
        funext g
        rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]
    _ = ∫ g : Formalism.REAL.UJ ε, ∫ x, φ (umat g) • ⟪f x, a w (act g x)⟫_ℂ ∂ν ∂(Formalism.REAL.muG ε) :=
        (integral_integral_swap (f := fun (g : Formalism.REAL.UJ ε) (x : X) => φ (umat g) • ⟪f x, a w (act g x)⟫_ℂ) hint).symm
    _ = _ := by
        congr 1
        funext g
        rw [integral_smul, key _ (sigma_mem hP hG hσ hw g.2)]
        simp only [hact']

end GlobalTheory.SmVec
