import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) : V' →L[ℂ] V :=
  (ContinuousLinearMap.adjoint Y).comp ((σ γ).comp Y')

theorem inner_sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) (a : V) (b : V') :
    ⟪a, sand σ Y Y' γ b⟫_ℂ = ⟪Y a, σ γ (Y' b)⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right Y a (σ γ (Y' b))

private theorem norm_sq_eq_sum_norm_inner_stdBasis_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (v : E) :
    ‖v‖ ^ 2 = ∑ i, ‖⟪stdOrthonormalBasis ℂ E i, v⟫_ℂ‖ ^ 2 := by
  exact ((stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right v).symm

theorem hsA_eq (A : V' →L[ℂ] V) :
    hsA A = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V i, A (stdOrthonormalBasis ℂ V' j)⟫_ℂ‖ ^ 2 := by
  show ∑ j, ‖A (stdOrthonormalBasis ℂ V' j)‖ ^ 2 = _
  exact Finset.sum_congr rfl fun j _ => norm_sq_eq_sum_norm_inner_stdBasis_sq _

theorem hsA_sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) :
    hsA (sand σ Y Y' γ) = ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 := by
  rw [hsA_eq]
  simp only [inner_sand]

theorem norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem schur_sq {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hS : IsSchur μ σ d) (a b : HH) :
    Integrable (fun γ => ‖⟪a, σ γ b⟫_ℂ‖ ^ 2) μ ∧
      ∫ γ, ‖⟪a, σ γ b⟫_ℂ‖ ^ 2 ∂μ = ‖a‖ ^ 2 * ‖b‖ ^ 2 / d := by
  obtain ⟨hI, hE⟩ := hS.2 b a b a
  have hfun : (fun γ => ‖⟪a, σ γ b⟫_ℂ‖ ^ 2) =
      fun γ => RCLike.re (⟪a, σ γ b⟫_ℂ * conj ⟪a, σ γ b⟫_ℂ) := by
    funext γ
    exact norm_sq_eq_re_mul_conj _
  have h2 : ∫ γ, RCLike.re (⟪a, σ γ b⟫_ℂ * conj ⟪a, σ γ b⟫_ℂ) ∂μ =
      RCLike.re (⟪b, b⟫_ℂ * ⟪a, a⟫_ℂ / (d : ℂ)) := by
    rw [← hE]
    exact integral_re hI
  have hsq : ∀ x : HH, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hI.re
  · rw [hfun, h2, hsq a, hsq b, ← Complex.ofReal_mul, ← Complex.ofReal_div]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    ring

theorem lintegral_hsA_sand {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hS : IsSchur μ σ d)
    (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) :
    ∫⁻ γ, ENNReal.ofReal (hsA (sand σ Y Y' γ)) ∂μ =
      ENNReal.ofReal ((∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2) / d) := by
  have hterm : ∀ j i,
      Integrable (fun γ => ‖⟪Y (stdOrthonormalBasis ℂ V i),
        σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2) μ ∧
      ∫ γ, ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
        ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2 * ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2 / d :=
    fun j i => schur_sq hS _ _
  have hInt : Integrable (fun γ => ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2) μ :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hterm j i).1
  have hrow : ∀ j, ∫ γ, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
      ∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2 * ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2 / d := by
    intro j
    rw [integral_finsetSum _ fun i _ => (hterm j i).1]
    exact Finset.sum_congr rfl fun i _ => (hterm j i).2
  have hval : ∫ γ, ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
      (∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2) / d := by
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hterm j i).1]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    simp only [Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_comm
  simp_rw [hsA_sand]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (ae_of_all _ fun γ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _), hval]

end Formalism.L2.S.Pv.EnergyAbs
