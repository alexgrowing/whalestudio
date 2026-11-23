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

namespace GlobalTheory.CompanionTheory.WcB.Indep

theorem rW_const_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (a b c d : F) (k : ℂ) (f : E → ℂ) (z : E) :
    GL2LocalData.rW χ σ μ lam a b c d (fun x => k * f x) z = k * GL2LocalData.rW χ σ μ lam a b c d f z := by
  unfold GL2LocalData.rW
  split_ifs with h
  · ring
  · have : (fun u => (χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) * (k * f u))
        = fun u => k * ((χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) * f u) := by
      funext u; ring
    rw [this, integral_const_mul]
    ring

theorem wS_indep : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ), Φ ∈ GL2LocalData.SBc F E c → ∀ (g : GL (Fin 2) F) (t t' : Eˣ), Algebra.norm F (t : E) = Algebra.norm F (t' : E) → wS χ σ μ lam c Φ g t = wS χ σ μ lam c Φ g t' := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hΦ g t t' hN
  have hu : Algebra.norm F ((t' * t⁻¹ : Eˣ) : E) = 1 := by
    have h1 : Algebra.norm F ((t' * t⁻¹ : Eˣ) : E) * Algebra.norm F (t : E) = Algebra.norm F (t : E) := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right, hN]
    have h2 : Algebra.norm F (t : E) ≠ 0 := ((t.isUnit).map (Algebra.norm F : E →* F)).ne_zero
    exact mul_right_cancel₀ h2 (h1.trans (one_mul _).symm)
  have hf : (fun x => Φ (x * (t' : E))) = fun x => (((c (t' * t⁻¹))⁻¹ : ℂˣ) : ℂ) * Φ (x * (t : E)) := by
    funext x
    rw [← hΦ.2.2 _ hu (x * (t : E))]
    congr 1
    rw [mul_assoc, ← Units.val_mul, mul_comm t, inv_mul_cancel_right]
  have hc : ((c t' : ℂˣ) : ℂ) = ((c t : ℂˣ) : ℂ) * ((c (t' * t⁻¹) : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← map_mul, mul_comm t, inv_mul_cancel_right]
  have hk : ((c (t' * t⁻¹) : ℂˣ) : ℂ) * (((c (t' * t⁻¹))⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  unfold wS
  rw [hf, rW_const_mul, hc]
  linear_combination (-((c t : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
    GL2LocalData.rW χ σ μ lam (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
      (fun x => Φ (x * (t : E))) 1) * hk

end GlobalTheory.CompanionTheory.WcB.Indep
