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

noncomputable section

namespace GlobalTheory.CompanionTheory.WcB.RwFormula

theorem rW_one_eq_gaussI : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E), σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ) (Φ : E → ℂ) (a b cc d : F), cc ≠ 0 → ∀ t : Eˣ, GL2LocalData.rW χ σ μ lam a b cc d (fun x => Φ (x * (t : E))) 1 = lam * GL2LocalData.nsg E (-cc) * (((modulus cc : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus (t : E) : ℝ)⁻¹ : ℝ) : ℂ) * (χ (a / cc) : ℂ) * gaussI χ μ Φ (d / (cc * Algebra.norm F (t : E))) ((algebraMap F E cc)⁻¹ * (t : E)⁻¹) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ _ μ _ lam Φ a b cc d hc t
  have hD : Algebra.norm F (t : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 t.ne_zero
  have hcE : algebraMap F E cc ≠ 0 := (map_ne_zero _).2 hc
  set κ : F := d / (cc * Algebra.norm F (t : E)) with hκ
  set ξ : E := (algebraMap F E cc)⁻¹ * (t : E)⁻¹ with hξ
  set f : E → ℂ := fun u => (χ (κ * Algebra.norm F u - Algebra.trace F E (ξ * u)) : ℂ) * Φ u with hf
  have key : ∀ u : E, (χ ((a * Algebra.norm F (1 : E) + d * Algebra.norm F u
        - Algebra.trace F E (σ 1 * u)) / cc) : ℂ) * Φ (u * (t : E))
      = (χ (a / cc) : ℂ) * f ((t : E) * u) := by
    intro u
    have hy : ξ * ((t : E) * u) = algebraMap F E cc⁻¹ * u := by
      rw [hξ, map_inv₀]
      field_simp
    have harg : (a * Algebra.norm F (1 : E) + d * Algebra.norm F u
        - Algebra.trace F E (σ 1 * u)) / cc
        = a / cc + (κ * Algebra.norm F ((t : E) * u)
          - Algebra.trace F E (ξ * ((t : E) * u))) := by
      have hN1 : Algebra.norm F (1 : E) = 1 := map_one _
      have hNtu : Algebra.norm F ((t : E) * u) = Algebra.norm F (t : E) * Algebra.norm F u :=
        map_mul _ _ _
      have hs1 : σ (1 : E) = 1 := map_one σ
      rw [hy, ← Algebra.smul_def, map_smul, smul_eq_mul, hNtu, hN1, hs1, one_mul, hκ]
      field_simp
      ring
    simp only [hf]
    rw [harg, AddChar.map_add_eq_mul, Circle.coe_mul, mul_comm u, mul_assoc]
  unfold GL2LocalData.rW gaussI
  rw [if_neg hc]
  simp only []
  rw [integral_congr_ae (Filter.Eventually.of_forall key), integral_const_mul,
    integral_comp_mul_left μ t.ne_zero f, Complex.real_smul]
  ring

end GlobalTheory.CompanionTheory.WcB.RwFormula
