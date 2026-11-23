import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftFunctionalLinearRootPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormPowEqSumMonomial

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

noncomputable section

namespace GlobalTheory.FlagPoly.FunctionalForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def degLin (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) : Pol ι N →ₗ[ℝ] ℝ where
  toFun := degFl ι N
  map_add' := PPowSum.degFl_add
  map_smul' c P := by
    rw [smul_eq_C_mul, PPowSum.degFl_C_mul]; rfl

def shLin (j : ℕ) (τ : ι) : Pol ι N →ₗ[ℝ] ℝ :=
  degLin ι N ∘ₗ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
    (pderiv (R := ℝ) (τ, i)).toLinearMap

def totLin (τ : ι) : Pol ι N →ₗ[ℝ] ℝ :=
  degLin ι N ∘ₗ ∑ i : Fin N, (pderiv (R := ℝ) (τ, i)).toLinearMap

theorem shLin_apply (j : ℕ) (τ : ι) (F : Pol ι N) : shLin j τ F = shF j τ F := by
  simp only [shLin, shF, LinearMap.comp_apply, LinearMap.sum_apply]
  rfl

theorem totLin_apply (τ : ι) (F : Pol ι N) : totLin τ F = totF τ F := by
  simp only [totLin, totF, LinearMap.comp_apply, LinearMap.sum_apply]
  rfl

omit [DecidableEq ι] in
theorem ev_invForm (j : ℕ) (al be : ι → ℝ) (lam : ι → Fin N → ℝ) :
    ev lam (invForm j al be) = ∑ τ, ((al τ - be τ) *
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), lam τ i + be τ * ∑ i, lam τ i) := by
  simp only [ev, invForm, pLow, pHigh, map_sum, map_add, map_mul, eval_C, pow_one, eval_X]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) (lam τ)]
  simp only [not_lt]
  ring

theorem functional_form : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (PP hh : Pol ι N →ₗ[ℝ] ℝ) (vol c : ℝ) (al be : ι → ℝ) (E : Pol ι N), CoefLe E c → (∀ lam, PP (linRoot lam ^ (dimFl ι N + 1)) = vol * (hh (linRoot lam ^ (dimFl ι N + 1)) + ((dimFl ι N : ℝ) + 1) * flagDeg ι N lam * ev lam (invForm j al be)) + ev lam E) → ∃ EE : Pol ι N →ₗ[ℝ] ℝ, (∀ m : (ι × Fin N) →₀ ℕ, m.degree = dimFl ι N + 1 → |EE (monomial m 1)| ≤ c) ∧ ∀ F : Pol ι N, PP F = vol * (hh F - ∑ τ, (al τ - be τ) * shF j τ F - ∑ τ, be τ * totF τ F) + EE F := by
  intro ι _ _ N j PP hh vol c al be E hE h
  let EE : Pol ι N →ₗ[ℝ] ℝ :=
    PP - vol • (hh - ∑ τ, (al τ - be τ) • shLin j τ - ∑ τ, be τ • totLin τ)
  have hEE : ∀ F, EE F =
      PP F - vol * (hh F - ∑ τ, (al τ - be τ) * shF j τ F - ∑ τ, be τ * totF τ F) := by
    intro F
    simp only [EE, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, shLin_apply,
      totLin_apply, smul_eq_mul]
  refine ⟨EE, fun m hm => ?_, fun F => by rw [hEE]; ring⟩
  refine (GlobalTheory.FlagPoly.coeff_eq_of_polarisation ι N (dimFl ι N + 1) EE E (fun lam => ?_) m hm).2.trans (hE m)
  rw [hEE, h, ev_invForm, sub_sub, ← Finset.sum_add_distrib, Finset.mul_sum]
  have : ∀ τ, (al τ - be τ) * shF j τ (linRoot lam ^ (dimFl ι N + 1)) +
      be τ * totF τ (linRoot lam ^ (dimFl ι N + 1)) =
      -(((dimFl ι N : ℝ) + 1) * flagDeg ι N lam * ((al τ - be τ) *
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), lam τ i + be τ * ∑ i, lam τ i)) := by
    intro τ
    rw [(GlobalTheory.T.shift_functional_linear_root_power ι N j lam τ).1, (GlobalTheory.T.shift_functional_linear_root_power ι N j lam τ).2]
    ring
  simp only [this, Finset.sum_neg_distrib]
  ring

end GlobalTheory.FlagPoly.FunctionalForm
