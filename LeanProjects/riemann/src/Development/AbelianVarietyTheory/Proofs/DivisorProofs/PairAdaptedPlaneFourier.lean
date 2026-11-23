import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlanePairRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlanePairInductionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.KernelBoundOnKDecay

theorem decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J, ∀ K : Set (UA σ X.J), IsCompact K → K ⊆ unip σ X H →
      ∀ K' : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ u ∈ K, ∀ h : UA σ W.J, ∀ N : ℕ, 1 ≤ N → ∀ w : Fin d → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
        ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖ * (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K' ≤ C * ((N : ℝ) * ht h) ^ k := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV hM₁ hev Φ hΦ g K hK
    hKs K'
  obtain ⟨N₀, k₀, C₀, hC₀⟩ := GlobalTheory.T.adelicThetaSum_norm_le_polynomial_scale F (Fin d₂ × Fin d)
  obtain ⟨C₁, k₁, h1⟩ := GlobalTheory.T.hyperbolic_plane_pair_restriction hKP F E σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hV hM₁ hev Φ hΦ g K hK hKs
  obtain ⟨C₂, k₂, h2⟩ := GlobalTheory.T.hyperbolic_plane_pair_induction hKP F E σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hV hM₁ hev Φ hΦ g K hK hKs
    N₀ K'
  refine ⟨max C₀ 0 * max C₂ 0 * max C₁ 0 ^ k₀, k₂ + k₁ * k₀, fun u hu h N hN w hw => ?_⟩
  obtain ⟨m, hm1, hmC, hmd⟩ := h1 u hu h N hN
  set S : ℝ := 1 + ∑ i, ∑ v : InfinitePlace E, v (w i) with hS
  have hS1 : 1 ≤ S := by
    have : 0 ≤ ∑ i, ∑ v : InfinitePlace E, v (w i) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun v _ => AbsoluteValue.nonneg _ _
    linarith
  have hSp : 0 < S ^ K' := pow_pos (by linarith) _
  set x : ℝ := (N : ℝ) * ht h with hxdef
  have hx : 1 ≤ x := by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hh : (1 : ℝ) ≤ ht h := by
      have := GlobalTheory.AdelicU.one_le_heightGL F h.1
      exact_mod_cast this
    nlinarith
  set Ψ := e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))) with hΨ
  have hA : ∀ ξ : Fin d₂ × Fin d → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ *
      (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ C₂ * x ^ k₂ / S ^ K' := by
    intro ξ
    rw [le_div_iff₀ hSp]
    exact h2 u hu h N hN w hw ξ
  have hA0 : 0 ≤ C₂ * x ^ k₂ / S ^ K' := by
    refine le_trans ?_ (hA 0)
    positivity
  have hth := hC₀ (C₂ * x ^ k₂ / S ^ K') m Ψ hm1 hA (fun ξ hξ => hmd w hw ξ hξ)
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₀ := by positivity
  have hmk : (m : ℝ) ^ k₀ ≤ max C₁ 0 ^ k₀ * x ^ (k₁ * k₀) := by
    rw [pow_mul, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) (hmC.trans ?_) _
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hC2 : C₂ * x ^ k₂ ≤ max C₂ 0 * x ^ k₂ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hC2' : 0 ≤ C₂ * x ^ k₂ := by
    have := mul_nonneg hA0 hSp.le
    rwa [div_mul_cancel₀ _ hSp.ne'] at this
  calc ‖thetaSum F Ψ‖ * S ^ K' ≤ (C₀ * (C₂ * x ^ k₂ / S ^ K') * (m : ℝ) ^ k₀) * S ^ K' :=
        mul_le_mul_of_nonneg_right hth hSp.le
    _ ≤ (max C₀ 0 * (C₂ * x ^ k₂ / S ^ K') * (m : ℝ) ^ k₀) * S ^ K' := by
        gcongr
        exact le_max_left _ _
    _ = max C₀ 0 * (C₂ * x ^ k₂) * (m : ℝ) ^ k₀ := by
        field_simp
    _ ≤ max C₀ 0 * (max C₂ 0 * x ^ k₂) * (max C₁ 0 ^ k₀ * x ^ (k₁ * k₀)) := by
        gcongr
    _ = max C₀ 0 * max C₂ 0 * max C₁ 0 ^ k₀ * x ^ (k₂ + k₁ * k₀) := by
        rw [pow_add]; ring

end GlobalTheory.KernelBoundOnKDecay
