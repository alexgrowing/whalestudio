import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFiniteDecompositionStable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_finite_decomposition_stable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ K : Subgroup (UA σ G.V.J), IsStab B K →
    ∀ Ψ ∈ schA F (Fin a × Fin (a + a')),
      ∃ (n : ℕ) (g : Fin n → (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) → ℂ) (S : Set (SInf F (Fin a × Fin (a + a'))))
        (f : K → Fin n → SInf F (Fin a × Fin (a + a'))), (∀ i, g i ∈ SB (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F)) ∧
        IsCompact S ∧ (∀ k i, f k i ∈ S) ∧ ∀ k : K, om (k.1, 1) Ψ = ∑ i, pureA F (f k i) (g i) := by
  first | exact @GlobalTheory.OrbitDecomp.exists_orbit_decomp | exact GlobalTheory.OrbitDecomp.exists_orbit_decomp | (intros; apply GlobalTheory.OrbitDecomp.exists_orbit_decomp <;> assumption)
