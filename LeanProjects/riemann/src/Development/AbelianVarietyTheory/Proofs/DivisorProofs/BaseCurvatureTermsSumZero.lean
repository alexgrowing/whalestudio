import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeWedgeAnticomm

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory.BaseSecondDeriv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def dEps (ε : ℂ) (φ : E → ℂ) (b v : E) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ φ b v + ε * fderiv ℝ φ b (Complex.I • v))

theorem d_one_zero_eq_dEps_neg_I (φ : E → ℂ) (b v : E) : d10 φ b v = dEps (-Complex.I) φ b v := by
  simp only [d10, dEps, smul_eq_mul]; ring

theorem d_zero_one_eq_dEps_I (φ : E → ℂ) (b v : E) : d01 φ b v = dEps Complex.I φ b v := by
  simp only [d01, dEps, smul_eq_mul]

theorem fderiv_dEps (ε : ℂ) {φ : E → ℂ} {b : E} (hφ : ContDiffAt ℝ 2 φ b) (v u : E) :
    fderiv ℝ (fun b' => dEps ε φ b' v) b u =
      (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ φ) b u v + ε * fderiv ℝ (fderiv ℝ φ) b u (Complex.I • v)) := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ φ) b :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : ∀ x : E, HasFDerivAt (fun b' => fderiv ℝ φ b' x)
      ((ContinuousLinearMap.apply ℝ ℂ x).comp (fderiv ℝ (fderiv ℝ φ) b)) b := fun x =>
    (ContinuousLinearMap.apply ℝ ℂ x).hasFDerivAt.comp b h1.hasFDerivAt
  have h3 := (((h2 v).fun_add ((h2 (Complex.I • v)).const_mul ε)).const_mul (1 / 2 : ℂ)).fderiv
  unfold dEps
  rw [h3]
  simp [mul_add]

theorem dEps_comm (ε δ : ℂ) {φ : E → ℂ} {b : E} (hφ : ContDiffAt ℝ 2 φ b) (v u : E) :
    dEps ε (fun b' => dEps δ φ b' v) b u = dEps δ (fun b' => dEps ε φ b' u) b v := by
  have hs : IsSymmSndFDerivAt ℝ φ b := hφ.isSymmSndFDerivAt (by simp)
  rw [dEps, dEps, fderiv_dEps δ hφ, fderiv_dEps δ hφ, fderiv_dEps ε hφ, fderiv_dEps ε hφ,
    hs u v, hs u (Complex.I • v), hs (Complex.I • u) v, hs (Complex.I • u) (Complex.I • v)]
  ring

theorem baseD_baseD_eq_zero {g n : ℕ} (β : Fin n → E) {φ : E → ℂ} {b : E}
    (hφ : ContDiffAt ℝ 2 φ b) (w : Ext (n + n + g)) :
    ∑ i, (baseD β (fun b' => d10 φ b' (β i)) b (wedge (dt g i) w) +
      baseD β (fun b' => d01 φ b' (β i)) b (wedge (dtb g i) w)) = 0 := by
  set F : Fin n → Fin n → Ext (n + n + g) := fun i k =>
    (wedge (dt g k) (d10 (fun b' => d10 φ b' (β i)) b (β k) • wedge (dt g i) w) +
      wedge (dtb g k) (d01 (fun b' => d10 φ b' (β i)) b (β k) • wedge (dt g i) w)) +
    (wedge (dt g k) (d10 (fun b' => d01 φ b' (β i)) b (β k) • wedge (dtb g i) w) +
      wedge (dtb g k) (d01 (fun b' => d01 φ b' (β i)) b (β k) • wedge (dtb g i) w)) with hF
  have h1 : ∑ i, (baseD β (fun b' => d10 φ b' (β i)) b (wedge (dt g i) w) +
      baseD β (fun b' => d01 φ b' (β i)) b (wedge (dtb g i) w)) = ∑ i, ∑ k, F i k := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [baseD, hF, ← Finset.sum_add_distrib]
  have h2 : ∀ i k, F i k = -F k i := by
    intro i k
    simp only [hF, wedge_smul, d_one_zero_eq_dEps_neg_I, d_zero_one_eq_dEps_I]
    rw [dEps_comm (-Complex.I) (-Complex.I) hφ (β i) (β k),
      dEps_comm Complex.I (-Complex.I) hφ (β i) (β k),
      dEps_comm (-Complex.I) Complex.I hφ (β i) (β k),
      dEps_comm Complex.I Complex.I hφ (β i) (β k),
      GlobalTheory.WedgeAnticomm.wedge_wedge_anticomm (dt g k) (dt g i),
      GlobalTheory.WedgeAnticomm.wedge_wedge_anticomm (dtb g k) (dt g i),
      GlobalTheory.WedgeAnticomm.wedge_wedge_anticomm (dt g k) (dtb g i),
      GlobalTheory.WedgeAnticomm.wedge_wedge_anticomm (dtb g k) (dtb g i)]
    simp only [smul_neg]
    abel
  have h3 : ∑ i, ∑ k, F i k = -∑ i, ∑ k, F i k := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => h2 k i
  rw [h1]
  have h4 : (2 : ℂ) • ∑ i, ∑ k, F i k = 0 := by
    rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h3
  exact (smul_eq_zero.1 h4).resolve_left two_ne_zero

end GlobalTheory.BaseSecondDeriv
