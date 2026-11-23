import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentCosetParametrization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotent_coset_parametrization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x₀ : Fin n → E), form σ J x₀ x₀ = 0 → x₀ ≠ 0 →
    ∀ γ : {x : Fin n → E // x ≠ 0 ∧ form σ J x x = 0} → UA σ J, (∀ x, γ x ∈ ratU σ J ∧ mat (γ x) *ᵥ incV F x.1 = incV F x₀) →
    ∀ δ ∈ ratU σ J, ∃! x, δ * (γ x)⁻¹ ∈ ratU σ J ⊓ Subgroup.closure {g : UA σ J | mat g *ᵥ incV F x₀ = incV F x₀} := by
  first | exact @GlobalTheory.ThK.IsoCoset.coset | exact GlobalTheory.ThK.IsoCoset.coset | (intros; apply GlobalTheory.ThK.IsoCoset.coset <;> assumption)
