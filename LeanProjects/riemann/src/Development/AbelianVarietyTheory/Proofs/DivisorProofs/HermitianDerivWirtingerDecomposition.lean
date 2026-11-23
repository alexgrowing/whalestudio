import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

namespace GlobalTheory.MatDeriv

theorem fderiv_entry_conj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}
    (H : E → Matrix (Fin m) (Fin m) ℂ) (w : E)
    (hH : ∀ᶠ w' in 𝓝 w, (H w').IsHermitian) (a b : Fin m)
    (hd : DifferentiableAt ℝ (fun w' => H w' b a) w) (ξ : E) :
    fderiv ℝ (fun w' => H w' a b) w ξ = (starRingEnd ℂ) (fderiv ℝ (fun w' => H w' b a) w ξ) := by
  have heq : (fun w' => H w' a b) =ᶠ[𝓝 w] (fun w' => Complex.conjCLE (H w' b a)) := by
    filter_upwards [hH] with w' hw'
    simp [← hw'.apply a b]
  rw [heq.fderiv_eq]
  have h2 := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := H w b a)).comp w hd.hasFDerivAt
  rw [show (fun w' => Complex.conjCLE (H w' b a)) = (Complex.conjCLE.toContinuousLinearMap ∘ fun w' => H w' b a) from rfl, h2.fderiv]
  simp

theorem dMat_eq_wirt_add_conjTranspose_wirt : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ} (H : E → Matrix (Fin m) (Fin m) ℂ) (w : E), (∀ᶠ w' in 𝓝 w, (H w').IsHermitian) → (∀ a b, DifferentiableAt ℝ (fun w' => H w' a b) w) → ∀ ξ : E, dMat H w ξ = wirt H w ξ + (wirt H w ξ)ᴴ := by
  intro E _ _ m H w hH hd ξ
  ext a b
  have h1 := fderiv_entry_conj H w hH b a (hd a b) ξ
  have h2 := fderiv_entry_conj H w hH b a (hd a b) (Complex.I • ξ)
  simp only [wirt, dMat, Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.of_apply, smul_eq_mul, star_mul', star_sub]
  rw [h1, h2]
  simp only [Complex.star_def, map_mul, map_sub, Complex.conj_conj, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

end GlobalTheory.MatDeriv
