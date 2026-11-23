import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqDiscriminantMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntisymmetricDiscriminantInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallOnWallsNearDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WallSetCompactDominantStatement

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

theorem ev_invForm_scale {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (j : ℕ) (al be : ι → ℝ) (k : ℝ)
    (lam : ι → Fin N → ℝ) :
    ev lam (invForm j (fun τ => k * al τ) (fun τ => k * be τ)) = k * ev lam (invForm j al be) := by
  simp only [ev, invForm, map_sum, map_add, map_mul, eval_C, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem near_flagDeg_mul_invForm_of_wall_bound :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 < C ∧ ∀ (P h : Pol ι N) (vol e : ℝ), 0 < vol → 0 ≤ e → P.IsHomogeneous (dimFl ι N + 1) → h.IsHomogeneous (dimFl ι N + 1) → AntiL j (P - MvPolynomial.C vol * h) → (∀ τ lam, Dom lam → GapZero j τ lam → ev lam h = 0) → (∀ τ, ∀ lam ∈ wallSet (N := N) j τ (1 / (4 * (N : ℝ))), |ev lam P| ≤ e) → ∃ (al be : ι → ℝ) (E : Pol ι N), E.IsHomogeneous (dimFl ι N + 1) ∧ CoefLe E (C * e) ∧ ∀ lam, ev lam P = vol * (ev lam h + ((dimFl ι N : ℝ) + 1) * flagDeg ι N lam * ev lam (invForm j al be)) + ev lam E := by
  intro ι _ _ N j hj hjN
  obtain ⟨K, hK, hlem⟩ := GlobalTheory.T.small_on_walls_near_discriminant ι N j hj hjN
  obtain ⟨c, hc, hdeg⟩ := GlobalTheory.T.flag_degree_eq_discriminant_multiple ι N
  refine ⟨K, hK, ?_⟩
  intro P h vol e hvol he hP hh hanti hzero hwall
  have hR : (P - MvPolynomial.C vol * h).IsHomogeneous (dimFl ι N + 1) := hP.sub (hh.C_mul vol)
  have hevR : ∀ lam, ev lam (P - MvPolynomial.C vol * h) = ev lam P - vol * ev lam h := by
    intro lam
    simp only [ev, map_sub, map_mul, eval_C]
  obtain ⟨al, be, hco⟩ := hlem (P - MvPolynomial.C vol * h) e he hR hanti (by
    intro τ lam hlam
    rw [hevR, hzero τ lam ((GlobalTheory.T.wall_set_compact_dominant ι N j τ hj hjN).2.1 lam hlam) hlam.2.1]
    simpa using hwall τ lam hlam)
  have hD : (0 : ℝ) < (dimFl ι N : ℝ) + 1 := by positivity
  refine ⟨fun τ => (vol * ((dimFl ι N : ℝ) + 1) * c)⁻¹ * al τ,
    fun τ => (vol * ((dimFl ι N : ℝ) + 1) * c)⁻¹ * be τ,
    P - MvPolynomial.C vol * h - delPol ι N * invForm j al be,
    hR.sub (GlobalTheory.T.antisymmetric_discriminant_invariant ι N j al be).2, hco, ?_⟩
  intro lam
  rw [ev_invForm_scale, hdeg lam]
  have : ev lam (P - MvPolynomial.C vol * h - delPol ι N * invForm j al be)
      = ev lam P - vol * ev lam h - ev lam (delPol ι N) * ev lam (invForm j al be) := by
    simp only [ev, map_sub, map_mul, eval_C]
  rw [this]
  field_simp
  ring

end GlobalTheory.FlagPoly
