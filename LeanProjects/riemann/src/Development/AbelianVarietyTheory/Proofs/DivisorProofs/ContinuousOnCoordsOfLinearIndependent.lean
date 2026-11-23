import Mathlib
open Filter Topology

namespace GlobalTheory

open Matrix

noncomputable def realDotC {g : ℕ} (u w : Fin g → ℂ) : ℝ :=
  ∑ k, ((u k).re * (w k).re + (u k).im * (w k).im)

lemma realDotC_comm {g : ℕ} (u w : Fin g → ℂ) : realDotC u w = realDotC w u := by
  unfold realDotC; refine Finset.sum_congr rfl (fun k _ => ?_); ring

lemma realDotC_sum_right {g m : ℕ} (u : Fin g → ℂ) (x : Fin m → ℝ) (μ : Fin m → Fin g → ℂ) :
    realDotC u (∑ i, x i • μ i) = ∑ i, x i * realDotC u (μ i) := by
  unfold realDotC
  simp only [Finset.sum_apply, Pi.smul_apply, Complex.re_sum, Complex.im_sum, Complex.smul_re,
    Complex.smul_im, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)); ring

lemma realDotC_self_eq_zero {g : ℕ} (u : Fin g → ℂ) (h : realDotC u u = 0) : u = 0 := by
  unfold realDotC at h
  have hn : ∀ k ∈ Finset.univ, 0 ≤ (u k).re * (u k).re + (u k).im * (u k).im :=
    fun k _ => by nlinarith [sq_nonneg (u k).re, sq_nonneg (u k).im]
  rw [Finset.sum_eq_zero_iff_of_nonneg hn] at h
  funext k
  have hk := h k (Finset.mem_univ _)
  apply Complex.ext <;> simp <;> nlinarith [sq_nonneg (u k).re, sq_nonneg (u k).im]

theorem continuousOn_coords_of_linearIndependent :
    ∀ (g m : ℕ) (U : Set ℂ) (μ : ℂ → Fin m → Fin g → ℂ) (v : ℂ → Fin g → ℂ) (c : ℂ → Fin m → ℝ),
      ContinuousOn μ U → ContinuousOn v U → (∀ s ∈ U, LinearIndependent ℝ (μ s)) →
      (∀ s ∈ U, v s = ∑ i, c s i • μ s i) → ContinuousOn c U := by
  intro g m U μ v c hμ hv hli hc
  rw [continuousOn_iff_continuous_restrict] at hμ hv ⊢
  let G : U → Matrix (Fin m) (Fin m) ℝ := fun s a b => realDotC (μ s a) (μ s b)
  let b : U → Fin m → ℝ := fun s a => realDotC (μ s a) (v s)
  have hdot : Continuous (fun p : (Fin g → ℂ) × (Fin g → ℂ) => realDotC p.1 p.2) := by
    unfold realDotC; fun_prop
  have hμa : ∀ a, Continuous (fun s : U => μ s a) := fun a => (continuous_apply a).comp hμ
  have hGc : Continuous G :=
    continuous_pi (fun a => continuous_pi (fun b' => hdot.comp ((hμa a).prodMk (hμa b'))))
  have hbc : Continuous b := continuous_pi (fun a => hdot.comp ((hμa a).prodMk hv))
  have hGc_eq : ∀ s : U, G s *ᵥ (c s) = b s := by
    intro s; funext a
    simp only [G, b, Matrix.mulVec, dotProduct]
    rw [hc s s.2, realDotC_sum_right]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
  have hdet : ∀ s : U, (G s).det ≠ 0 := by
    intro s hd
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    apply hx0
    have hw : ∑ i, x i • μ s i = 0 := by
      apply realDotC_self_eq_zero
      rw [realDotC_sum_right]
      have key : ∀ i, realDotC (μ s i) (∑ j, x j • μ s j) = (G s *ᵥ x) i := by
        intro i; rw [realDotC_sum_right]; simp only [G, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl (fun j _ => ?_); ring
      simp_rw [realDotC_comm _ (μ s _), key, hx]; simp
    funext i
    exact Fintype.linearIndependent_iff.mp (hli s s.2) x hw i
  have hceq : U.domRestrict c = fun s => ((G s).det)⁻¹ • ((G s).adjugate *ᵥ b s) := by
    funext s
    have h1 : c s = (G s)⁻¹ *ᵥ b s := by
      rw [← hGc_eq s, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet s)), Matrix.one_mulVec]
    show c s = _
    rw [h1, Matrix.inv_def, Ring.inverse_eq_inv']
    ext a; simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Finset.mul_sum, mul_assoc]
  rw [hceq]
  exact (hGc.matrix_det.inv₀ hdet).smul (hGc.matrix_adjugate.matrix_mulVec hbc)

end GlobalTheory
