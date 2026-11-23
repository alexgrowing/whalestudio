import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

noncomputable section

open Filter Topology Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.HermFrame
open scoped Matrix ContDiff

namespace GlobalTheory.ChernCalc.FrameChange

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable {r : Type*} [Fintype r] [DecidableEq r] {H A B : E → Matrix r r ℂ} {z : E}

theorem conn_mul_mul (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 1 A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt 1 B z) (hBu : IsUnit (B z).det)
    (hB0 : ∀ η, mdbar B z η = 0) (ξ : E) :
    conn (fun x => A x * H x * (B x)ᴴ) z ξ = (A z)ᵀ⁻¹ * (conn H z ξ * (A z)ᵀ + (mdel A z ξ)ᵀ) := by
  refine (eq_conn_of_compatible ?_ ?_).symm
  · simp only [det_mul, det_conjTranspose]
    exact (hAu.mul hu).mul hBu.star
  · rw [mdel_mul (hA.mul h) hB.conjTranspose, mdel_mul hA h, mdel_conjTranspose, hB0, ← conn_transpose_mul hu,
      transpose_mul, transpose_nonsing_inv]
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hAu, transpose_add, transpose_mul, Matrix.add_mul,
      conjTranspose_zero, transpose_transpose, Matrix.mul_zero, zero_add]

theorem curv_mul_mul (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det) (hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0)
    (hB : MContDiffAt 2 B z) (hBu : IsUnit (B z).det) (hB0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar B x η = 0) (ξ η : E) :
    curv (fun x => A x * H x * (B x)ᴴ) z ξ η = (A z)ᵀ⁻¹ * curv H z ξ η * (A z)ᵀ := by
  have he : (fun x => conn (fun x => A x * H x * (B x)ᴴ) x ξ) =ᶠ[𝓝 z]
      fun x => (A x)ᵀ⁻¹ * (conn H x ξ * (A x)ᵀ + (mdel A x ξ)ᵀ) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, hA.eventually_two,
      hA.eventually_isUnit hAu, hB.eventually_two, hB.eventually_isUnit hBu, hB0] with x h1 h2 h3 h4 h5 h6 h7
    exact conn_mul_mul (h1.of_le one_le_two) h2 (h3.of_le one_le_two) h4 (h5.of_le one_le_two) h6 h7 ξ
  have hA1 : MContDiffAt 1 (fun x => (A x)ᵀ) z := (hA.of_le one_le_two).transpose
  have hAu' : IsUnit (A z)ᵀ.det := by rwa [det_transpose]
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have hd : MContDiffAt 1 (fun x => (mdel A x ξ)ᵀ) z := (hA.mdel (by norm_num) ξ).transpose
  have h0 : mddbar A z ξ η = 0 := by
    rw [← mdel_mdbar hA, mdel_congr (B := fun _ => 0) (hA0.mono fun x hx => hx η), mdel_const]
  rw [curv, mdbar_congr he, mdbar_mul (hA1.inv hAu') ((hc.mul hA1).add hd), mdbar_inv hA1 hAu',
    mdbar_add (hc.mul hA1) hd, mdbar_mul hc hA1, mdbar_transpose (fun x => mdel A x ξ), mdbar_mdel hA, h0,
    mdbar_transpose A, hA0.self_of_nhds, curv]
  simp [Matrix.mul_assoc]

end General

variable {n : ℕ} {r : Type} [Fintype r] {T : V n → Matrix r r ℂ} {v : V n}

omit [Fintype r] in

theorem two_of_holo (h : ∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) : MContDiffAt 2 T v :=
  fun a b => ((SCV.analyticAt_iff_eventually_differentiableAt.2 (h a b)).contDiffAt).restrict_scalars ℝ

theorem mdbar_zero_of_holo (h : ∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) :
    ∀ᶠ x in 𝓝 v, ∀ η, mdbar T x η = 0 :=
  (eventually_all.2 fun a => eventually_all.2 fun b => h a b).mono fun x hx η => by
    ext a b
    rw [mdbar_apply, dbar_eq_zero (hx a b)]
    rfl

theorem conn_curv_frame : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G₂ T K : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ) → (∀ ξ, conn G₂ v ξ = (T v)ᵀ⁻¹ * (conn G v ξ * (T v)ᵀ + (mdel T v ξ)ᵀ)) ∧ ∀ ξ η, curv G₂ v ξ η = (T v)ᵀ⁻¹ * curv G v ξ η * (T v)ᵀ := by
  intro n r _ _ G G₂ T K v hG hGu hT hTu hK hKu he
  have hG2 : MContDiffAt 2 G v := hG.of_le (by norm_cast)
  refine ⟨fun ξ => ?_, fun ξ η => ?_⟩
  · rw [conn_congr he]
    exact conn_mul_mul (hG2.of_le one_le_two) hGu ((two_of_holo hT).of_le one_le_two) hTu
      ((two_of_holo hK).of_le one_le_two) hKu (mdbar_zero_of_holo hK).self_of_nhds ξ
  · rw [curv_congr he]
    exact curv_mul_mul hG2 hGu (two_of_holo hT) hTu (mdbar_zero_of_holo hT) (two_of_holo hK) hKu
      (mdbar_zero_of_holo hK) ξ η

end GlobalTheory.ChernCalc.FrameChange
