import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.AntitoneOfMemInterl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.RmCharacter

open ReciprocityTheory.ChartRestriction.TR.Weyl PositivityTheory.RgBcC

theorem gtChar_zero : ∀ (n : ℕ) (t : Fin n → ℂ), gtChar n (0 : Fin n → ℤ) t = 1
  | 0, _ => by simp [gtChar]
  | n + 1, t => by
    have h : interl (0 : Fin (n + 1) → ℤ) = {(0 : Fin n → ℤ)} := by
      ext mu
      simp only [interl, Fintype.mem_piFinset, Pi.zero_apply, Finset.Icc_self, Finset.mem_singleton]
      exact ⟨fun h => funext h, fun h i => congrFun h i⟩
    rw [gtChar, h, Finset.sum_singleton, gtChar_zero n]
    simp [wsum]

theorem wden_ne_zero {n : ℕ} {t : Fin n → ℂ} (ht : Function.Injective t) : wden n t ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  split_ifs with h
  · exact sub_ne_zero.2 fun e => h.ne (ht e)
  · exact one_ne_zero

theorem alt_num {n : ℕ} (lam : Fin n → ℤ) (t : Fin n → ℂ) :
    alt n (lam + delta n) t = (Matrix.of fun i j : Fin n => t i ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det := by
  unfold alt
  congr 1
  refine Matrix.ext fun i j => ?_
  have hj := j.2
  simp only [Matrix.of_apply, Pi.add_apply, delta]
  congr 2
  omega

theorem alt_den {n : ℕ} (t : Fin n → ℂ) :
    alt n ((0 : Fin n → ℤ) + delta n) t = (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))).det := by
  unfold alt
  congr 1
  refine Matrix.ext fun i j => ?_
  have hj := j.2
  simp only [Matrix.of_apply, Pi.add_apply, Pi.zero_apply, delta, zero_add]
  rw [← zpow_natCast]
  congr 1
  omega

theorem weylChar_eq_gtChar {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) (t : Fin n → ℂ) (h0 : ∀ a, t a ≠ 0)
    (ht : Function.Injective t) : weylChar lam t = gtChar n lam t := by
  have hnum := weylGT ℂ n lam hlam t h0
  have hden := weylGT ℂ n (0 : Fin n → ℤ) (fun _ _ _ => le_rfl) t h0
  rw [gtChar_zero, mul_one, alt_den] at hden
  rw [alt_num] at hnum
  rw [weylChar, ← hnum, ← hden, mul_div_cancel_left₀ _ (wden_ne_zero ht)]

theorem rmChar : RmChar := by
  intro n lam hlam t h0 ht
  have hu : IsUnit (diagonal t : Matrix (Fin n) (Fin n) ℂ).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => h0 a)
  have hw : (dw lam).w = lam := by
    simp only [dw, dif_pos hlam]
  rw [Rm, dif_pos hu, ← LinearMap.trace_eq_matrix_trace, weylChar_eq_gtChar lam hlam t h0 ht,
    GlobalTheory.ContraChar.trace_sqRep_diag (dw lam) _ t rfl, hw]

end GlobalTheory.CompanionTheory.RmCharacter
