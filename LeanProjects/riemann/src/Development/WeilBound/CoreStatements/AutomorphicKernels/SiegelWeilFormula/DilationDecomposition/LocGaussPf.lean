import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Imports
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem gauss_int_one (δ : ℝ) (hδ : 0 < δ) : Integrable (fun z : ℂ => Real.exp (-δ * ‖z‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (δ : ℂ))
    (by simpa using hδ) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  rw [show (-(δ : ℂ) * (‖z‖ : ℂ) ^ 2) = ((-δ * ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

theorem gauss_int_row {n : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2)) := by
  exact Integrable.fintype_prod (f := fun _ (z : ℂ) => Real.exp (-δ * ‖z‖ ^ 2))
    (fun _ => gauss_int_one δ hδ)

theorem gauss_int_mat {m n : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-δ * ‖v a j‖ ^ 2)) := by
  exact Integrable.fintype_prod (f := fun _ (w : Fin n → ℂ) => ∏ j, Real.exp (-δ * ‖w j‖ ^ 2))
    (fun _ => gauss_int_row δ hδ)

theorem gauss_int_pf {m n : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => Real.exp (-δ * sq v)) := by
  refine (gauss_int_mat (m := m) (n := n) δ hδ).congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [PositivityTheory.SiegelWeilFormula.Kdil.sq, Finset.mul_sum, ← Real.exp_sum]

theorem gauss_int_closed : type_of% @gauss_int_pf := @gauss_int_pf

end PositivityTheory.SiegelWeilFormula.Kdil

end
