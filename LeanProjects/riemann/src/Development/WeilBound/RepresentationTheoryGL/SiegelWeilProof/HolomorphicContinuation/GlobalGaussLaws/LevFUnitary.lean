import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RotDG
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRCosSubSin

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacH

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG

theorem row_norm {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u * uᴴ = 1) (x : Fin n → ℂ) :
    ∑ j, ((‖∑ k, x k * u k j‖ ^ 2 : ℝ) : ℂ) = ∑ k, ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h1]
  have hu2 : ∀ k l, ∑ j, u k j * star (u l j) = if k = l then 1 else 0 := by
    intro k l
    have h := congrFun (congrFun hu k) l
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  calc ∑ j, (∑ k, x k * u k j) * star (∑ k, x k * u k j)
      = ∑ j, ∑ k, ∑ l, x k * star (x l) * (u k j * star (u l j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [star_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [star_mul']
        ring
    _ = ∑ k, ∑ l, x k * star (x l) * ∑ j, u k j * star (u l j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k, x k * star (x k) := by
        simp only [hu2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem levF_unitary {m n : ℕ} (e : ℤ) (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (K γ0 : ℂ) :
    levF e u (DG (m := m) (n := n) K (fun _ _ => γ0)) =
      DG (K * (u.det ^ e * (star u.det) ^ ((m : ℤ) - e))) (fun _ _ => γ0) := by
  funext v
  have hu' : u * uᴴ = 1 := mul_eq_one_comm.mp hu
  have key : ∀ a : Fin m, ∏ j : Fin n, Complex.exp (-γ0 * ((‖(Matrix.of v * u) a j‖ ^ 2 : ℝ) : ℂ))
      = ∏ j : Fin n, Complex.exp (-γ0 * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_sum, ← Complex.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    simpa [Matrix.mul_apply] using row_norm u hu' (v a)
  simp only [levF, DG, key]
  ring

theorem dbl_angle (ρ x : ℝ) (hρ : ρ ^ 2 = 1) :
    ((Real.cos (x / 2) : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin (x / 2) : ℂ)) *
      ((Real.cos (x / 2) : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin (x / 2) : ℂ)) =
    (Real.cos x : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin x : ℂ) := by
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_two_mul (x / 2)
  have hp := Real.sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc hs
  rw [hc, hs]
  generalize Real.cos (x / 2) = c at *
  generalize Real.sin (x / 2) = s at *
  push_cast
  have hp' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hp
  have hρ' : (ρ : ℂ) ^ 2 = 1 := by exact_mod_cast hρ
  linear_combination (-1 : ℂ) * hp' + (s : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * Complex.I_sq - (s : ℂ) ^ 2 * hρ'

end PositivityTheory.Rg.Sw.Glob.VacH
