import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarLocalFactor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_evaluation_haar_local_factor : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, ∀ (c : Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F) (S : K → (AE F E)ˣ → SchwartzMap (Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) ℂ),
        (∀ k l s, S k l s = e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))
            (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s i), c i) : AdeleRing (𝓞 F) F)) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) →
        ∀ m n : ℕ, ∃ C : (AE F E)ˣ → ℝ, Continuous C ∧ Integrable C μ ∧ ∀ k l, SchwartzMap.seminorm ℂ m n (S k l) ≤ C l := by
  first | exact @GlobalTheory.ConeSliceBound.seminorm_slice_le | exact GlobalTheory.ConeSliceBound.seminorm_slice_le | (intros; apply GlobalTheory.ConeSliceBound.seminorm_slice_le <;> assumption)
