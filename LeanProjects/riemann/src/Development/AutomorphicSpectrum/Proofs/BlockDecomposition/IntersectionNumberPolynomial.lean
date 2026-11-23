import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.CompanionTheory.ChernPoly

theorem inter_add_nsmul_polynomial :
    ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv), ∃ Q : Polynomial ℝ, ∀ m : ℕ,
      ((Y.inter fun _ => Δ + m • Δ₀ : ℤ) : ℝ) = Q.eval (m : ℝ) := by
  intro Y Δ Δ₀
  classical
  refine ⟨∑ s : Finset (Fin Y.dim),
    Polynomial.C ((Y.interForm (s.piecewise (fun _ => Δ₀) (fun _ => Δ)) : ℤ) : ℝ) * Polynomial.X ^ s.card,
    fun m => ?_⟩
  have h1 : (fun _ : Fin Y.dim => Δ + m • Δ₀) = (fun _ => (m : ℤ) • Δ₀) + (fun _ => Δ) := by
    funext i
    rw [Pi.add_apply, natCast_zsmul, add_comm]
  rw [← Y.interForm_apply, h1, MultilinearMap.map_add_univ]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : (s.piecewise (fun i => (m : ℤ) • s.piecewise (fun _ => Δ₀) (fun _ => Δ) i)
      (s.piecewise (fun _ => Δ₀) (fun _ => Δ))) = s.piecewise (fun _ => (m : ℤ) • Δ₀) (fun _ => Δ) := by
    funext i
    by_cases hi : i ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ hi,
        Finset.piecewise_eq_of_mem _ _ _ hi]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi,
        Finset.piecewise_eq_of_notMem _ _ _ hi]
  have key := Y.interForm.map_piecewise_smul (fun _ => (m : ℤ)) (s.piecewise (fun _ => Δ₀) (fun _ => Δ)) s
  rw [hpw, Finset.prod_const, smul_eq_mul] at key
  rw [key]
  push_cast
  ring

end GlobalTheory.CompanionTheory.ChernPoly
