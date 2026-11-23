import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBd
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology

namespace GlobalTheory

theorem jensen_log_mean : ∀ {d : ℕ} (q g : (Fin d → ℂ) → ℝ), Continuous q → (∀ (t : ℝ) ξ, q (t • ξ) = t ^ 2 * q ξ) → (∀ ξ, ξ ≠ 0 → 0 < q ξ) → (∀ ξ, 1 ≤ g ξ) → MeasureTheory.Integrable (fun ξ => g ξ * GlobalTheory.ChernReg.cutoff (q ξ)) → MeasureTheory.Integrable (fun ξ => Real.log (g ξ) * GlobalTheory.ChernReg.cutoff (q ξ)) → GlobalTheory.ChernReg.mean q (fun ξ => Real.log (g ξ)) ≤ Real.log (GlobalTheory.ChernReg.mean q g) := by
  intro d q g hc hh hp hg hgi hli
  have hχ : MeasureTheory.Integrable (fun ξ => GlobalTheory.ChernReg.cutoff (q ξ)) := integrable_cutoff hc hh hp
  have hm0 : 0 < ∫ ξ, GlobalTheory.ChernReg.cutoff (q ξ) := mass_pos hc hh hp
  have hgm : (∫ ξ, GlobalTheory.ChernReg.cutoff (q ξ)) ≤ ∫ ξ, g ξ * GlobalTheory.ChernReg.cutoff (q ξ) :=
    integral_mono hχ hgi (fun ξ => by
      have := cutoff_nonneg (q ξ)
      have := hg ξ
      show GlobalTheory.ChernReg.cutoff (q ξ) ≤ g ξ * GlobalTheory.ChernReg.cutoff (q ξ)
      nlinarith)
  have hM0 : 0 < GlobalTheory.ChernReg.mean q g := div_pos (hm0.trans_le hgm) hm0
  set M := GlobalTheory.ChernReg.mean q g with hM
  have key : ∀ ξ, Real.log (g ξ) * GlobalTheory.ChernReg.cutoff (q ξ) ≤
      Real.log M * GlobalTheory.ChernReg.cutoff (q ξ) +
        (g ξ * GlobalTheory.ChernReg.cutoff (q ξ) - M * GlobalTheory.ChernReg.cutoff (q ξ)) / M := by
    intro ξ
    have hgpos : 0 < g ξ := lt_of_lt_of_le one_pos (hg ξ)
    have h1 := Real.log_le_sub_one_of_pos (div_pos hgpos hM0)
    rw [Real.log_div hgpos.ne' hM0.ne'] at h1
    have hc0 := cutoff_nonneg (q ξ)
    have h2 : g ξ / M - 1 = (g ξ - M) / M := by field_simp; try ring
    have h3 : Real.log (g ξ) ≤ Real.log M + (g ξ - M) / M := by linarith
    calc Real.log (g ξ) * GlobalTheory.ChernReg.cutoff (q ξ)
        ≤ (Real.log M + (g ξ - M) / M) * GlobalTheory.ChernReg.cutoff (q ξ) := mul_le_mul_of_nonneg_right h3 hc0
      _ = _ := by field_simp; try ring
  have hI1 : MeasureTheory.Integrable (fun ξ => Real.log M * GlobalTheory.ChernReg.cutoff (q ξ)) := hχ.const_mul _
  have hI2 : MeasureTheory.Integrable (fun ξ => M * GlobalTheory.ChernReg.cutoff (q ξ)) := hχ.const_mul _
  have hI3 : MeasureTheory.Integrable
      (fun ξ => (g ξ * GlobalTheory.ChernReg.cutoff (q ξ) - M * GlobalTheory.ChernReg.cutoff (q ξ)) / M) := (hgi.sub hI2).div_const M
  have hint : (∫ ξ, Real.log (g ξ) * GlobalTheory.ChernReg.cutoff (q ξ)) ≤ ∫ ξ, (Real.log M * GlobalTheory.ChernReg.cutoff (q ξ) +
        (g ξ * GlobalTheory.ChernReg.cutoff (q ξ) - M * GlobalTheory.ChernReg.cutoff (q ξ)) / M) := integral_mono hli (hI1.add hI3) key
  rw [integral_add hI1 hI3, integral_div, integral_sub hgi hI2, integral_const_mul, integral_const_mul] at hint
  have hMm : M * (∫ ξ, GlobalTheory.ChernReg.cutoff (q ξ)) = ∫ ξ, g ξ * GlobalTheory.ChernReg.cutoff (q ξ) := by
    rw [hM, GlobalTheory.ChernReg.mean]; field_simp; try ring
  rw [hMm, sub_self, zero_div, add_zero] at hint
  rw [GlobalTheory.ChernReg.mean, div_le_iff₀ hm0]
  exact hint

end GlobalTheory
