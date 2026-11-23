import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem gram_change (R : RiemLat E g Λ) {m : ℕ} (bb d : Fin m → Fin g → ℂ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (hd : ∀ b, d b = ∑ c, Y c b • bb c) : R.gram d = Yᴴ * R.gram bb * Y := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RiemLat.gram, Matrix.of_apply, RiemLat.ip, hd,
    star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem log_det_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (bb d : Fin m → Fin g → ℂ) (Y M : Matrix (Fin m) (Fin m) ℂ) (κ : ℝ), 0 < κ → (∀ b, d b = ∑ c, Y c b • bb c) → R.gram d * M = (κ : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) → M.PosDef → Y.det ≠ 0 ∧ -Real.log M.det.re = 2 * Real.log ‖Y.det‖ + Real.log (R.gram bb).det.re - m * Real.log κ := by
  intro E _ _ _ g Λ _ _ R m bb d Y M κ hκ hd hM hpos
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, gram_change R bb d Y hd, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hMp : 0 < M.det := hpos.det_pos
  obtain ⟨hr, hi⟩ := Complex.pos_iff.mp hMp
  set r := M.det.re with hrdef
  have hMr : M.det = (r : ℂ) := by
    apply Complex.ext <;> simp [hrdef, ← hi]
  set y := Y.det with hy
  set G := (R.gram bb).det with hG
  have hyy : star y * y = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' y
  have hκm : 0 < κ ^ m := pow_pos hκ m
  have e1 : ((‖y‖ ^ 2 : ℝ) : ℂ) * G * (r : ℂ) = ((κ ^ m : ℝ) : ℂ) := by
    rw [← hyy, ← hMr]
    push_cast
    linear_combination hdet
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at e1
    have : ((κ ^ m : ℝ) : ℂ) = 0 := by simpa using e1.symm
    exact hκm.ne' (by exact_mod_cast this)
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hGr : G = ((κ ^ m / (‖y‖ ^ 2 * r) : ℝ) : ℂ) := by
    have h2 : ((‖y‖ ^ 2 * r : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pow_pos hn 2) hr).ne'
    push_cast at h2 e1 ⊢
    field_simp
    linear_combination e1
  refine ⟨hy0, ?_⟩
  rw [hGr, Complex.ofReal_re, Real.log_div hκm.ne' (mul_pos (pow_pos hn 2) hr).ne',
    Real.log_mul (pow_pos hn 2).ne' hr.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog
