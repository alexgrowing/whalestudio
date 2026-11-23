import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSpanFunctionInterpolationBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarLevelMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarLocalFactorStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.ConeDecompWeil

theorem cone_integrand_decomp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h,
      ∃ (r : ℕ) (g : Fin r → (Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F) → ℂ)
        (f : Fin r → K → (AE F E)ˣ → SchwartzMap (Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) ℂ),
        (∀ j, g j ∈ SB (Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F)) ∧
        (∀ k l y, e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) y * (X.ν l : ℂ) *
            ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) = ∑ j, pureA F (f j k l) (g j) y) ∧
        (∀ j (T : SchwartzMap (Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ),
          Continuous (fun p : K × (AE F E)ˣ => T (f j p.1 p.2))) ∧
        (∀ j (m n : ℕ), ∃ c : (AE F E)ˣ → ℝ, Continuous c ∧ Integrable c μ ∧ ∀ k l, SchwartzMap.seminorm ℂ m n (f j k l) ≤ c l) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  obtain ⟨r, g, hg, hspan⟩ := GlobalTheory.T.seesaw_evaluation_haar_unfolding hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  obtain ⟨r', g', c, hg'span, hlag⟩ := GlobalTheory.T.finite_span_function_interpolation_basis _ r g
  choose S hS hSc using fun j : Fin r' =>
    GlobalTheory.T.seesaw_evaluation_haar_level_measure hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h (c j)
  have hle : Submodule.span ℂ (Set.range g) ≤ SB (Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hg)
  refine ⟨r', g', S, fun j => hle (hg'span j), ?_, hSc, fun j m n =>
    GlobalTheory.T.seesaw_evaluation_haar_local_factor hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h (c j) (S j) (hS j) m n⟩
  intro k l y
  have key : e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) y = ∑ j, e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) (fun i => (((y i).1, c j i) : AdeleRing (𝓞 F) F)) *
      g' j (fun i => (y i).2) := hlag _ (hspan k l (fun i => (y i).1)) (fun i => (y i).2)
  simp only [pureA, hS, RingEquiv.symm_apply_apply]
  rw [key]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.ConeDecompWeil

end
