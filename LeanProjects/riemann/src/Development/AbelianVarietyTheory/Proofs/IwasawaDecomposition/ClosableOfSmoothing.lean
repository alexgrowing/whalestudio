import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem closable_of_smoothing : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : H →ₗ[ℂ] E), (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ⟪A (σ g u), A (σ g w)⟫_ℂ = ⟪A u, A w⟫_ℂ) → (∀ u ∈ smSub G (trRep σ P), ∀ f : E, Continuous fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ) → (∀ φ, IsTest φ → Continuous fun w => A (gard ε σ φ w)) → (∀ φ, IsTest φ → ∀ w ∈ smSub G (trRep σ P), ∀ f : E, ⟪f, A (gard ε σ φ w)⟫_ℂ = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪f, A (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε)) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) := by
  intro n ε H _ _ _ σ P G hP hG hσ E _ _ A h1 h2 h3 h4 u f hu hu0 hA
  have hmul : ∀ (g : Formalism.REAL.UJ ε) (v : H), σ (umat g) (σ (umat g⁻¹) v) = v := by
    intro g v
    have e : σ (umat g * umat g⁻¹) = _ := hσ.1.2 _ g.2 _ (g⁻¹).2
    have e1 : umat g * umat g⁻¹ = 1 := by
      have : umat (g * g⁻¹) = umat (1 : Formalism.REAL.UJ ε) := by rw [mul_inv_cancel]
      exact this
    rw [e1, hσ.1.1] at e
    exact (congrArg (fun T : H →L[ℂ] H => T v) e).symm
  have key : ∀ v ∈ smSub G (trRep σ P), ⟪A v, f⟫_ℂ = 0 := by
    intro v hv
    have hmem : ∀ g : Formalism.REAL.UJ ε, σ (umat g⁻¹) v ∈ smSub G (trRep σ P) := fun g =>
      sigma_mem hP hG hσ hv (g⁻¹).2
    have hc : ∀ y : E, Continuous fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), y⟫_ℂ := by
      intro y
      have := Complex.continuous_conj.comp ((h2 v hv y).comp continuous_inv)
      simpa only [Function.comp_def, inner_conj_symm] using this
    have hnorm : ∀ g : Formalism.REAL.UJ ε, ‖A (σ (umat g⁻¹) v)‖ = ‖A v‖ := by
      intro g
      have := h1 _ (g⁻¹).2 v hv v hv
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (A v)]
      exact congrArg (fun z => √(RCLike.re z)) this
    have h0 := eq_zero_of_forall_test (F := fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), f⟫_ℂ) (hc f) (by
      intro φ hφ
      have hg0 : gard ε σ φ 0 = 0 := by simp [gard]
      have t1 : Tendsto (fun i => ⟪A v, A (gard ε σ φ (u i))⟫_ℂ) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := A v)).inner (𝕜 := ℂ) (((h3 φ hφ).tendsto 0).comp hu0)
        simpa [hg0, Function.comp_def] using this
      have e : ∀ i, ⟪A v, A (gard ε σ φ (u i))⟫_ℂ
          = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), A (u i)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
        intro i
        rw [h4 φ hφ _ (hu i)]
        congr 1
        funext g
        rw [← h1 _ g.2 _ (hmem g) _ (hu i)]
        erw [hmul]
      have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) (Formalism.REAL.muG ε) := by
        simpa using hφ.integrable (F := fun _ : Formalism.REAL.UJ ε => (1 : ℝ)) continuous_const
      have t2 : Tendsto (fun i => ⟪A v, A (gard ε σ φ (u i))⟫_ℂ) atTop
          (𝓝 (∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), f⟫_ℂ ∂(Formalism.REAL.muG ε))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have t3 : Tendsto (fun i => (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε)) * (‖A v‖ * ‖A (u i) - f‖))
            atTop (𝓝 0) := by
          have := ((tendsto_iff_norm_sub_tendsto_zero.1 hA).const_mul ‖A v‖).const_mul
            (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε))
          simpa using this
        refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) t3
        rw [e, ← integral_sub (hφ.integrable (hc _)) (hφ.integrable (hc _)), ← integral_mul_const]
        refine norm_integral_le_of_norm_le (hψi.norm.mul_const _) (Eventually.of_forall fun g => ?_)
        rw [← smul_sub, norm_smul, ← inner_sub_right, ← hnorm g]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      exact tendsto_nhds_unique t2 t1)
    have e : σ (umat (1 : Formalism.REAL.UJ ε)⁻¹) v = v := by
      rw [inv_one]
      show σ 1 v = v
      rw [hσ.1.1]; rfl
    simpa only [e] using h0
  have t := hA.inner (𝕜 := ℂ) (tendsto_const_nhds (x := f))
  simp only [key _ (hu _)] at t
  exact inner_self_eq_zero.1 (tendsto_nhds_unique t tendsto_const_nhds)

end GlobalTheory.SmVec
