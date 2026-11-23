import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.FourKFub

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem secondCountableK [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

theorem stdChar_continuous (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : ψ y = ψ x * ψ (y - x) := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
  rw [this, hψ.1 (y - x) (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy), mul_one]

theorem psiK_continuous (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous (A.psiK ψ) :=
  (stdChar_continuous ψ hψ).comp (IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K))

theorem psiK_add (A : Et F E) (ψ : AddChar F ℂ) (x y : A.K) : A.psiK ψ (x + y) = A.psiK ψ x * A.psiK ψ y := by
  simp only [Et.psiK, map_add, AddChar.map_add_eq_mul]

theorem fourK_eq_fourB_tilde : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → ∀ b c : A.K, A.fourK μK ψ φ' (b, c) = fourB μK (A.kerK ψ) (fun c' => A.tilde μK ψ φ' c' c) b := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ b c
  haveI := secondCountableK A
  have hc := psiK_continuous A ψ hψ
  let f : A.K × A.K → ℂ := fun p => φ' p * A.psiK ψ (b * p.2 + p.1 * c)
  have hf : Integrable f (μK.prod μK) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hφ.1.continuous.mul (hc.comp (by fun_prop))
    · exact hφ.2.mul_right
  simp only [Et.fourK, fourB, Et.tilde, Et.kerK]
  rw [integral_integral_swap (f := fun b' c' => φ' (b', c') * A.psiK ψ (b * c' + b' * c)) hf]
  refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
  simp only
  rw [psiK_add, mul_comm b c', mul_comm b' c]
  ring

end GlobalTheory.FourKFub
