import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneConditionsHermitian
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_plane_conditions_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d₂ : ℕ) (X : Spc F E n)
    (H : Plane E n d₂), (∀ i j, σ (X.J j i) = X.J i j) → (∀ e : E, σ (σ e) = e) →
      (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
      ∀ u : UA σ X.J, mat u *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin d₂ → AE F E, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) →
      ∀ (m m' : UA σ X.J) (t : ℕ),
      mat m *ᵥ incV F H.x = (2 : AE F E) • incV F H.x → (2 : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin d₂ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      mat m' *ᵥ incV F H.x = (t : AE F E) • incV F H.x → (t : AE F E) • (mat m' *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin d₂ → AE F E, mat m' *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      m' * (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) * m'⁻¹ = (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) ^ (t ^ 2) := by
  first | exact @GlobalTheory.UnipLineHyp.conj_commutator_eq_pow | exact GlobalTheory.UnipLineHyp.conj_commutator_eq_pow | (intros; apply GlobalTheory.UnipLineHyp.conj_commutator_eq_pow <;> assumption)
