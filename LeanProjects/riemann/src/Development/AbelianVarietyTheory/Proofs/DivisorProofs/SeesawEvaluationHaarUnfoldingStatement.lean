import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarUnfolding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_evaluation_haar_unfolding : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h,
      ∃ (r : ℕ) (g : Fin r → (Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F) → ℂ),
        (∀ j, g j ∈ SB (Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ (k : K) (l : (AE F E)ˣ) (s : Fin b × Fin (a + b) → InfiniteAdeleRing F),
          (fun z : Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F =>
            e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) (fun i => ((s i, z i) : AdeleRing (𝓞 F) F))) ∈ Submodule.span ℂ (Set.range g) := by
  first | exact @GlobalTheory.ConeFinSlices.finite_slices | exact GlobalTheory.ConeFinSlices.finite_slices | (intros; apply GlobalTheory.ConeFinSlices.finite_slices <;> assumption)
