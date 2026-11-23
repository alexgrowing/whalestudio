import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFramesStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem UpT.diag_ne_zero {n : ℕ} {b : Mt n} (hb : UpT b) (a : Fin n) : b a a ≠ 0 := by
  have hdet : b.det = ∏ i, b i i := Matrix.det_of_upperTriangular (fun i j hij => hb.2 i j hij)
  have h := hb.1
  rw [hdet, Finset.prod_ne_zero_iff] at h
  exact h a (Finset.mem_univ a)

theorem holFn_integral : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → (ι → Mt n) → ℂ) (C : ℝ), (∀ o, HolFn Hm q x₀ w (f o)) → (∀ o, ∀ u ∈ UG Hm, ‖f o u‖ ≤ C) → (∀ u ∈ UG Hm, AEStronglyMeasurable (fun o => f o u) ν) → HolFn Hm q x₀ w fun u => ∫ o, f o u ∂ν := by
  intro n ι _ _ Hm q x₀ w hx Ω _ ν _ f C hf hC hmeas

  have hf' : ∀ o, ∃ P, HolSec Hm q w P ∧ ∀ u ∈ UG Hm, f o u = P fun τ => (u τ * x₀ τ : Mt n) := hf
  choose Pc hPc using hf'

  have hβ := fun τ => GlobalTheory.T.smooth_gram_schmidt_indefinite_hermitian_frames n (Hm τ) (q τ) (x₀ τ) (hx τ)
  choose β hβc hβ using hβ
  obtain ⟨hopen, -, hmul, hx0⟩ := GlobalTheory.T.negativeFrameDomainProduct_open_preconnected_stable n ι Hm q x₀ hx

  let uu : (ι → Fin n → Fin n → ℂ) → ι → Mt n :=
    fun y τ => Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹ * (x₀ τ)⁻¹
  let cc : (ι → Fin n → Fin n → ℂ) → ℂ := fun y => ∏ τ, ∏ a, (β τ (y τ)) a a ^ w τ a
  have huu : ∀ y ∈ frDoms Hm q, uu y ∈ UG Hm := fun y hy τ => (hβ τ (y τ) (hy τ)).2

  have hkey : ∀ o, ∀ y ∈ frDoms Hm q, Pc o y = cc y * f o (uu y) := by
    intro o y hy
    have hu := huu y hy
    have hone : ∀ _τ : ι, UpT (1 : Mt n) := fun _ =>
      ⟨by simp, fun a c hca => Matrix.one_apply_ne (ne_of_gt hca)⟩
    have hfr : (fun τ => (uu y τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
      have := hmul (uu y) hu (fun _ => 1) hone (fun τ => (x₀ τ : Mt n)) hx0
      simp only [Matrix.mul_one] at this
      exact this
    have hB : ∀ τ, UpT (Matrix.of (β τ (y τ))) := fun τ => (hβ τ (y τ) (hy τ)).1
    have heq := (hPc o).1.2 (fun τ => (uu y τ * x₀ τ : Mt n)) hfr
      (fun τ => Matrix.of (β τ (y τ))) hB
    have hrec : (fun τ => (Matrix.of ((uu y τ * x₀ τ : Mt n)) * Matrix.of (β τ (y τ)) : Mt n)) = y := by
      funext τ
      have hX : (x₀ τ)⁻¹ * x₀ τ = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hx0 τ).1)
      have hBB : (Matrix.of (β τ (y τ)))⁻¹ * Matrix.of (β τ (y τ)) = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hB τ).1)
      show Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹ * (x₀ τ)⁻¹ * x₀ τ * Matrix.of (β τ (y τ)) = y τ
      rw [Matrix.mul_assoc (Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹), hX, Matrix.mul_one,
        Matrix.mul_assoc, hBB, Matrix.mul_one]
      rfl
    rw [hrec] at heq
    rw [heq, ← (hPc o).2 (uu y) hu]
    rfl

  have hcc : ContinuousOn cc (frDoms Hm q) := by
    apply continuousOn_finset_prod
    intro τ _
    apply continuousOn_finset_prod
    intro a _
    have h1 : ContinuousOn (fun y : ι → Fin n → Fin n → ℂ => β τ (y τ)) (frDoms Hm q) :=
      (hβc τ).continuousOn.comp (continuous_apply τ).continuousOn (fun y hy => hy τ)
    have h2 : ContinuousOn (fun y : ι → Fin n → Fin n → ℂ => β τ (y τ) a a) (frDoms Hm q) :=
      (show Continuous fun M : Fin n → Fin n → ℂ => M a a from
        (continuous_apply a).comp (continuous_apply a)).comp_continuousOn h1
    exact h2.zpow₀ _ (fun y hy => Or.inl (UpT.diag_ne_zero (hβ τ (y τ) (hy τ)).1 a))
  have hPmeas : ∀ y ∈ frDoms Hm q, AEStronglyMeasurable (fun o => Pc o y) ν := by
    intro y hy
    have : (fun o => Pc o y) = fun o => cc y * f o (uu y) := funext fun o => hkey o y hy
    rw [this]
    exact (hmeas (uu y) (huu y hy)).const_mul (cc y)
  have hdom : ∀ x ∈ frDoms Hm q, ∃ s ∈ 𝓝 x, ∃ bound : Ω → ℝ, Integrable bound ν ∧
      ∀ᵐ o ∂ν, ∀ y ∈ s, ‖Pc o y‖ ≤ bound o := by
    intro x hxm
    have hca : ContinuousAt cc x := hcc.continuousAt (hopen.mem_nhds hxm)
    have hev : ∀ᶠ y in 𝓝 x, ‖cc y‖ < ‖cc x‖ + 1 :=
      hca.norm.eventually (Iio_mem_nhds (lt_add_one _))
    refine ⟨{y | ‖cc y‖ < ‖cc x‖ + 1} ∩ frDoms Hm q, Filter.inter_mem hev (hopen.mem_nhds hxm),
      fun _ => (‖cc x‖ + 1) * max C 0, integrable_const _, Filter.Eventually.of_forall ?_⟩
    intro o y hy
    rw [hkey o y hy.2, norm_mul]
    exact mul_le_mul hy.1.le (le_max_of_le_left (hC o (uu y) (huu y hy.2))) (norm_nonneg _)
      (by positivity)
  unfold HolFn HolSec
  refine ⟨fun y => ∫ o, Pc o y ∂ν, ⟨?_, ?_⟩, ?_⟩
  · exact (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated hopen hPmeas
      (Filter.Eventually.of_forall fun o => (hPc o).1.1) hdom).1
  · intro x hxm b hb
    calc ∫ o, Pc o (fun τ => (Matrix.of (x τ) * b τ : Mt n)) ∂ν
        = ∫ o, (∏ τ, ∏ a, b τ a a ^ w τ a) * Pc o x ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall fun o => (hPc o).1.2 x hxm b hb)
      _ = (∏ τ, ∏ a, b τ a a ^ w τ a) * ∫ o, Pc o x ∂ν := integral_const_mul _ _
  · intro u hu
    exact integral_congr_ae (Filter.Eventually.of_forall fun o => (hPc o).2 u hu)

end GlobalTheory.HolDict
