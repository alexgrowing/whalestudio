import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTwistHomotopyKernel

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar.OpenCone

variable {n : ℕ}

theorem hOf_herm (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian := by
  show (hOf v)ᴴ = hOf v
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

theorem im_form {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    conv_rhs => rw [Matrix.star_dotProduct]
    rw [Matrix.star_mulVec, hM.eq, ← Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h

theorem continuous_form :
    Continuous fun z : (Fin n × Fin n → ℝ) × (Fin n → ℂ) => (star z.2 ⬝ᵥ hOf z.1 *ᵥ z.2).re := by
  have hent : ∀ i j : Fin n, Continuous fun v : Fin n × Fin n → ℝ => hOf v i j := by
    intro i j
    have : (fun v : Fin n × Fin n → ℝ => hOf v i j) = fun v => ∑ p, (v p : ℂ) * hb p i j := by
      funext v
      simp [hOf, Matrix.sum_apply]
    rw [this]
    fun_prop
  have hent' : ∀ i j : Fin n,
      Continuous fun z : (Fin n × Fin n → ℝ) × (Fin n → ℂ) => hOf z.1 i j :=
    fun i j => (hent i j).comp continuous_fst
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine Complex.continuous_re.comp ?_
  refine continuous_finset_sum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul ?_
  refine continuous_finset_sum _ fun j _ => ?_
  exact (hent' i j).mul ((continuous_apply j).comp continuous_snd)

theorem posDef_of_sphere {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian)
    (h : ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ M *ᵥ x).re) : M.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hM, fun x hx => ?_⟩
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hy : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp [hn]
  have h1 := h _ hy
  have h2 : star (((‖x‖⁻¹ : ℝ) : ℂ) • x) ⬝ᵥ M *ᵥ (((‖x‖⁻¹ : ℝ) : ℂ) • x) =
      (((‖x‖⁻¹ ^ 2 : ℝ)) : ℂ) * (star x ⬝ᵥ M *ᵥ x) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [smul_eq_mul, pow_two]
    ring
  rw [h2, Complex.re_ofReal_mul] at h1
  have h3 : 0 < (star x ⬝ᵥ M *ᵥ x).re := by
    have : 0 < ‖x‖⁻¹ ^ 2 := by positivity
    exact (pos_iff_pos_of_mul_pos h1).1 this
  exact Complex.pos_iff.2 ⟨h3, (im_form hM x).symm⟩

end GlobalTheory.CompanionTheory.ConeHaar.OpenCone

namespace GlobalTheory.CompanionTheory.ConeHaar

open OpenCone

theorem isOpen_cone : ∀ n : ℕ, IsOpen (PositivityTheory.RgBcC.cone n) := by
  intro n
  rw [isOpen_iff_eventually]
  intro v hv
  have hpos : ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ hOf v *ᵥ x).re := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 hv).2 hx0
    exact (Complex.pos_iff.1 this).1
  have hev : ∀ᶠ w in 𝓝 v, ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1,
      0 < (star x ⬝ᵥ hOf w *ᵥ x).re :=
    (isCompact_sphere (0 : Fin n → ℂ) 1).eventually_forall_of_forall_eventually fun x hx =>
      (continuous_form.continuousAt (x := (v, x))).eventually (lt_mem_nhds (hpos x hx))
  exact hev.mono fun w hw => posDef_of_sphere (hOf_herm w) hw

end GlobalTheory.CompanionTheory.ConeHaar
