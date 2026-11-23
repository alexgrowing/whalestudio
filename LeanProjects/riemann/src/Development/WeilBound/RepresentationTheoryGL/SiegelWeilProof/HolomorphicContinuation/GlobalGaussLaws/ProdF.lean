import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RhoTSq

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH
  PositivityTheory.Rg.Sw.Glob.VacI PositivityTheory.Rg.Sw.Glob.VacJ

theorem prodF {m n : ℕ} (t : ℝ) (ε : Fin m → Bool) (φ : Fin n → ℝ) :
    ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT t ε a : ℂ) * (Real.sin (φ j) : ℂ)) =
      (∏ j, Complex.exp (Complex.I * (φ j : ℂ))) ^ (cnt (epsT t ε) true) *
        ((∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹) ^ (cnt (epsT t ε) false) := by
  have inner : ∀ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT t ε a : ℂ) * (Real.sin (φ j) : ℂ)) =
      if epsT t ε a = true then ∏ j, Complex.exp (Complex.I * (φ j : ℂ))
      else (∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹ := by
    intro a
    by_cases h : epsT t ε a = true
    · rw [if_pos h]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [rhoT, if_pos h]
      rw [show Complex.I * (φ j : ℂ) = (φ j : ℂ) * Complex.I by ring, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
      push_cast
      ring
    · rw [if_neg h, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [rhoT, if_neg h]
      rw [← Complex.exp_neg, show -(Complex.I * (φ j : ℂ)) = (-(φ j : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
  rw [Finset.prod_congr rfl (fun a _ => inner a), Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp only [cnt, Bool.not_eq_true]

theorem alg (a a' X : ℂ) (ha : a ≠ 0) (ha' : a' ≠ 0) (hX : X ≠ 0) (e : ℤ) (p q : ℕ) :
    1 * (a' ^ e * (a'⁻¹) ^ (((p + q : ℕ) : ℤ) - e)) * (X ^ p * (X⁻¹) ^ q) * (a ^ e * (a⁻¹) ^ (((p + q : ℕ) : ℤ) - e)) =
      (a * a * (a' * a')) ^ e * (a * X⁻¹ * a') ^ (-(p : ℤ)) * (a * X * a') ^ (-(q : ℤ)) := by
  rw [inv_zpow', inv_zpow', neg_sub, zpow_sub₀ ha, zpow_sub₀ ha']
  simp only [zpow_neg, zpow_natCast, mul_zpow, inv_pow, mul_pow]
  have hA : a ^ e ≠ 0 := zpow_ne_zero e ha
  have hA' : a' ^ e ≠ 0 := zpow_ne_zero e ha'
  have hXp : X ^ p ≠ 0 := pow_ne_zero p hX
  have hXq : X ^ q ≠ 0 := pow_ne_zero q hX
  field_simp
  ring

end PositivityTheory.Rg.Sw.Glob.VacK
