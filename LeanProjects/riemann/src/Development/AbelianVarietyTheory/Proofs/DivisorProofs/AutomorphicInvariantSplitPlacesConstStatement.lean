import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicInvariantSplitPlacesConst
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_invariant_split_places_const : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (V : Spc F E n) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s → ∀ (T : Finset (Pl F)) (φ : UA σ V.J → ℂ), Continuous φ →
    (∀ γ ∈ ratU σ V.J, ∀ g, φ (γ * g) = φ g) →
    (∀ v : Pl F, v ∉ T → SplitsFully E v → ∀ g, ∀ k ∈ UAt σ V (evFin F v), φ (g * k) = φ g) → ∀ g g', φ g = φ g' := by
  first | exact @GlobalTheory.HermConstLift.constant_of_invariant | exact GlobalTheory.HermConstLift.constant_of_invariant | (intros; apply GlobalTheory.HermConstLift.constant_of_invariant <;> assumption)
