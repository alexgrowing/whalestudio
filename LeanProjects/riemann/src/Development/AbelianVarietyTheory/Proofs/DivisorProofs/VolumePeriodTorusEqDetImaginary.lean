import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

noncomputable section
namespace GlobalTheory.PerVol

def reIm {g : ℕ} (z : Fin g → ℂ) : Fl g := Sum.elim (fun i => (z i).im) (fun i => (z i).re)

theorem reIm_mp {g : ℕ} : MeasurePreserving (reIm (g := g)) volume volume := by
  have h1 : MeasurePreserving (fun (z : Fin g → ℂ) (i : Fin g) => Complex.measurableEquivRealProd (z i))
      volume volume :=
    volume_preserving_pi (fun _ : Fin g => Complex.volume_preserving_equiv_real_prod)
  have h2 := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin g)
  have h3 : MeasurePreserving (Prod.swap : (Fin g → ℝ) × (Fin g → ℝ) → _) volume volume :=
    Measure.measurePreserving_swap
  have h4 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin g ⊕ Fin g => ℝ)
  have := h4.comp (h3.comp (h2.comp h1))
  convert this using 1
  funext z i
  cases i <;> rfl

theorem reIm_injective {g : ℕ} : Function.Injective (reIm (g := g)) := by
  intro z w h
  funext i
  apply Complex.ext
  · exact congrFun h (Sum.inr i)
  · exact congrFun h (Sum.inl i)

def perMat {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  Matrix.fromBlocks (τ0.map Complex.im)ᵀ 0 (τ0.map Complex.re)ᵀ 1

theorem reIm_per {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) :
    reIm (per τ0 x) = Matrix.toLin' (perMat τ0) x := by
  funext i
  cases i with
  | inl i =>
    simp [reIm, per, perMat, Matrix.vecMul, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
      Matrix.fromBlocks, Complex.im_sum, Complex.re_sum, mul_comm]
  | inr i =>
    simp [reIm, per, perMat, Matrix.vecMul, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
      Matrix.fromBlocks, Complex.im_sum, Complex.re_sum, mul_comm, Matrix.one_apply]

theorem det_perMat {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) :
    (perMat τ0).det = (τ0.map Complex.im).det := by
  simp [perMat, Matrix.det_fromBlocks_zero₁₂]

end GlobalTheory.PerVol

namespace GlobalTheory.PerVol

theorem volume_per_image_Icc {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) :
    volume (per τ0 '' Set.Icc (0 : Fl g) 1) = ENNReal.ofReal |(τ0.map Complex.im).det| := by
  set L : Fl g →ₗ[ℝ] Fl g := Matrix.toLin' (perMat τ0)
  have hset : per τ0 '' Set.Icc (0 : Fl g) 1 = reIm ⁻¹' (L '' Set.Icc (0 : Fl g) 1) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (reIm_per τ0 x).symm⟩
    · rintro ⟨x, hx, hxz⟩
      refine ⟨x, hx, reIm_injective ?_⟩
      rw [reIm_per]
      exact hxz
  have hmeas : MeasurableSet (L '' Set.Icc (0 : Fl g) 1) :=
    (isCompact_Icc.image (LinearMap.continuous_of_finiteDimensional L)).measurableSet
  rw [hset, reIm_mp.measure_preimage hmeas.nullMeasurableSet,
    MeasureTheory.Measure.addHaar_image_linearMap, Real.volume_Icc_pi]
  simp [L, LinearMap.det_toLin', det_perMat]

end GlobalTheory.PerVol
