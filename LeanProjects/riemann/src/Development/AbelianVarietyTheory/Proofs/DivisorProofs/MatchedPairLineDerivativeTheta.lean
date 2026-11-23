import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInfinitePlaceApproxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineDerivativeSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Filter Topology

noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaOrbit

theorem pureA_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    pureA F ⇑(c • f) g = c • pureA F ⇑f g := by
  funext x
  simp [pureA, mul_assoc]

theorem orbit : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ γ ∈ Lines σ G.W, ∀ Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Φ₁ : (Fin a' × Fin (a + a') → AF F) → ℂ, (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → ∃ (m : ℕ) (φ : Fin m → (Fin a' × Fin (a + a') → Af F) → ℂ) (f : ℝ → Fin m → SInf F (Fin a' × Fin (a + a'))) (f₁ : Fin m → SInf F (Fin a' × Fin (a + a'))), (∀ i, φ i ∈ SB (Fin a' × Fin (a + a') → Af F)) ∧ (∀ t : ℝ, om' (1, γ (Multiplicative.ofAdd t)) Φ = ∑ i, pureA F (f t i) (φ i)) ∧ Φ₁ = ∑ i, pureA F (f₁ i) (φ i) ∧ ∀ i, Tendsto (fun t : ℝ => t⁻¹ • (f t i - f 0 i)) (𝓝[≠] 0) (𝓝 (f₁ i)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hd
  have hsch := GlobalTheory.KDecayProof.so_le_schA hM.triple.geo.hM' B.τ₁ (Submodule.mem_inf.1 hΦ).2
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hsch
  choose f0 φ hφ hfe using fun i => (g i).2
  choose u hu using fun (t : ℝ) (i : Fin n) => GlobalTheory.T.schwartz_infinite_place_approx hP F E σ B a a' G X om om' R Rf hM (γ (Multiplicative.ofAdd t)) (hγ.2 _) (c i • f0 i)
  have hu' : ∀ i, ∀ t : ℝ, ∀ g' ∈ SB (Fin a' × Fin (a + a') → Af F), om' (1, γ (Multiplicative.ofAdd t)) (pureA F (c i • f0 i) g') = pureA F (u t i) g' :=
    fun i t => hu t i
  choose u₁ hu₁ using fun i => GlobalTheory.T.theta_line_derivative_schwartz hP F E σ B a a' G X om om' R Rf hM γ hγ (c i • f0 i) (fun t => u t i) (hu' i)
  have hΦe : Φ = ∑ i, pureA F (c i • f0 i) (φ i) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfe i, pureA_smul]
  have horb : ∀ t : ℝ, om' (1, γ (Multiplicative.ofAdd t)) Φ = ∑ i, pureA F (u t i) (φ i) := by
    intro t
    rw [hΦe, map_sum]
    exact Finset.sum_congr rfl fun i _ => hu t i (φ i) (hφ i)
  refine ⟨n, φ, u, u₁, hφ, horb, ?_, hu₁⟩
  funext x
  set y : Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F := fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1
  set z : Fin a' × Fin (a + a') → Af F := fun j => (x j).2
  have hev : ∀ (s : SInf F (Fin a' × Fin (a + a'))) (ψ : (Fin a' × Fin (a + a') → Af F) → ℂ), pureA F s ψ x = s y * ψ z :=
    fun _ _ => rfl
  have hder : ∀ i, HasDerivAt (fun t : ℝ => u t i y) (u₁ i y) 0 := by
    intro i
    rw [hasDerivAt_iff_tendsto_slope]
    let ev : SInf F (Fin a' × Fin (a + a')) →L[ℂ] ℂ := (BoundedContinuousFunction.evalCLM ℂ y).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)
    have h1 := (ev.continuous.tendsto (u₁ i)).comp (hu₁ i)
    have e2 : ev (u₁ i) = u₁ i y := rfl
    rw [e2] at h1
    refine h1.congr' (Eventually.of_forall fun t => ?_)
    simp [ev, slope_def_module]
  have hsum : HasDerivAt (fun t : ℝ => ∑ i, u t i y * φ i z) (∑ i, u₁ i y * φ i z) 0 :=
    HasDerivAt.fun_sum fun i _ => (hder i).mul_const _
  have e1 : (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) = fun t => ∑ i, u t i y * φ i z := by
    funext t
    rw [horb, Finset.sum_apply]
    rfl
  have := hd x
  rw [e1] at this
  rw [this.unique hsum, Finset.sum_apply]
  rfl

end GlobalTheory.ThetaOrbit
