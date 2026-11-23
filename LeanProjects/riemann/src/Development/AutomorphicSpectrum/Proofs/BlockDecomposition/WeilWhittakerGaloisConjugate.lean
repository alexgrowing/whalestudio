import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology
open scoped NNReal

namespace GlobalTheory.CompanionTheory.WcB

theorem value_lower_zero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ), IsUnit1 c → ∀ g : GL (Fin 2) F, g.val 1 0 = 0 → GL2LocalData.Wc χ σ μ lam c Φ g ≠ 0 → ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det ∧ ‖GL2LocalData.Wc χ σ μ lam c Φ g‖ = (modulus (g.val).det : ℝ) ^ (1 / 2 : ℝ) * (modulus (g.val 1 1) : ℝ)⁻¹ * ‖Φ (algebraMap F E (g.val 1 1)⁻¹ * (t : E))‖ := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hc g h10 hW
  classical
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · refine ⟨h.choose, h.choose_spec, ?_⟩
    have hdet : (g.val).det = g.val 0 0 * g.val 1 1 := by
      rw [Matrix.det_fin_two, h10]; ring
    have hd0 : (g.val).det ≠ 0 := by
      have := g.isUnit
      exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
    have h00 : g.val 0 0 ≠ 0 := fun h0 => hd0 (by rw [hdet, h0, zero_mul])
    have h11 : g.val 1 1 ≠ 0 := fun h0 => hd0 (by rw [hdet, h0, mul_zero])
    have ha : g.val 0 0 / (g.val).det = (g.val 1 1)⁻¹ := by
      rw [hdet]; field_simp
    have hct : ‖((c h.choose : ℂˣ) : ℂ)‖ = 1 := hc.2 _
    have hn : ∀ a : F, ‖GL2LocalData.nsg E a‖ = 1 := by
      intro a
      unfold GL2LocalData.nsg
      split_ifs <;> simp
    have hpos : (0 : ℝ) < (modulus (g.val).det : ℝ) := by
      exact_mod_cast modulus_pos hd0
    have hcp : ‖(((modulus (g.val).det : ℝ) : ℂ)) ^ (1 / 2 : ℂ)‖ = (modulus (g.val).det : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      norm_num
    have hm : ‖(((modulus (g.val 1 1)⁻¹ : ℝ≥0) : ℝ) : ℂ)‖ = (modulus (g.val 1 1) : ℝ)⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _), modulus_inv, NNReal.coe_inv]
    rw [Wc_eq_wS χ σ μ lam c Φ g h]
    unfold wS GL2LocalData.rW
    rw [h10, zero_div, if_pos rfl, ha]
    simp only [norm_mul, hct, hcp, hn, hm, Circle.norm_coe, mul_one, one_mul]
    ring
  · exact absurd (Wc_eq_zero χ σ μ lam c Φ g h) hW

end GlobalTheory.CompanionTheory.WcB
