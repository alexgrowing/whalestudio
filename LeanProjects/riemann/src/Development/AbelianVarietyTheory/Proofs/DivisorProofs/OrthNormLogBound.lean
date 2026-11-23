import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBoundIffOrthBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingListCharacterProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InitMinorNeZeroOfStrictMono

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.BrCompare GlobalTheory.BrCompare.Shift

noncomputable section

namespace GlobalTheory.BranchLogBound

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

def sgN (lam : DomWeight (n + 1)) (sg : DomWeight n) : Fin n → ℕ := fun i => (sg.w i - lam.w (Fin.last n)).toNat

theorem interlace_w (h : Br.Interlace rfl lam sg) : Formalism.BranchingDeterminantCap.Interlace lam.w sg.w := by
  intro i
  have : 0 ≤ sg.w i - lam.w i.succ ∧ 0 ≤ lam.w i.castSucc - sg.w i := h i
  omega

theorem sgN_cast (h : Br.Interlace rfl lam sg) (i : Fin n) : (sgN lam sg i : ℤ) = sg.w i - lam.w (Fin.last n) := by
  have h1 := (interlace_w h i).2
  have h2 := lam.anti (Fin.le_last i.succ)
  unfold sgN
  omega

theorem interlace_N (h : Br.Interlace rfl lam sg) : Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sgN lam sg i : ℤ)) := by
  intro i
  have := interlace_w h i
  simp only [lamZ_lamN, sgN_cast h]
  omega

theorem xiBr_eq (h : Br.Interlace rfl lam sg) (K : Type) [Field K] :
    Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) (sgN lam sg)) := by
  have hb : ∀ s, (Br.bBr rfl lam sg s).toNat = lamN lam s - sgN lam sg s := by
    intro s
    have h1 := lamN_cast lam s
    have h2 := sgN_cast h s
    have h3 : Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s := rfl
    rw [h3]
    omega
  have ha : ∀ s, (Br.aBr rfl lam sg s).toNat = sgN lam sg s - nuNext (lamN lam) s := by
    intro s
    have h1 := nuNext_cast lam s
    have h2 := sgN_cast h s
    have h3 : Br.aBr rfl lam sg s = sg.w s - lam.w s.succ := rfl
    rw [h3]
    omega
  unfold Br.xiBr xiB
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]
  congr 2

theorem extremal_eq (lam : DomWeight (n + 1)) (K : Type) [Field K] :
    extremal K (n + 1) lam = incl K n (hw K (Nat.le_succ n) (lamN lam)) := by
  unfold extremal hw
  rw [map_prod, Fin.prod_univ_castSucc]
  have h0 : lam.natW (Fin.last n) = 0 := by
    have := natW_top lam (Fin.last n)
    omega
  rw [h0, Nat.zero_sub, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]
  congr 1
  · exact (rename_initMinor K (Fin.castLE (by have := i.2; omega) : Fin (i.val + 1) → Fin (n + 1)) (by have := i.2; omega)).symm
  · have h1 := nuNext_cast lam i
    have h2 := natW_top lam i.succ
    have h3 : nuNext lam.natW i.castSucc = lam.natW i.succ := by
      unfold nuNext
      rw [dif_pos (by simp)]
      rfl
    rw [h3]
    have h4 : lamN lam i = lam.natW i.castSucc := rfl
    omega

theorem fockF_map {σ : Type} (f : MvPolynomial σ ℝ) :
    (Formalism.REAL.fockF (map (algebraMap ℝ ℂ) f) (map (algebraMap ℝ ℂ) f)).re = fockB f f := by
  unfold Formalism.REAL.fockF fockB
  rw [support_map_of_injective _ (algebraMap ℝ ℂ).injective, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : ∀ (x : ℝ) (k : ℕ), ((algebraMap ℝ ℂ x) * (starRingEnd ℂ) (algebraMap ℝ ℂ x) * (k : ℂ)).re = x * x * k := by
    intro x k
    simp
  rw [coeff_map]
  exact this _ _

theorem map_xiB (l s : Fin n → ℕ) : map (algebraMap ℝ ℂ) (xiB ℝ l s) = xiB ℂ l s := by
  simp only [xiB, map_prod, map_mul, map_pow, initMinor, RingHom.map_det]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 3 <;> ext1 a b <;> simp

theorem kap_bounds (h : Br.Interlace rfl lam sg) :
    0 < Br.kapBr ℝ rfl lam sg ∧ Br.kapBr ℝ rfl lam sg ≤ weylProd (lamZ (lamN lam)) := by
  have h1 := xiNorm n (lamN lam) (sgN lam sg) (interlace_N h)
  have h2 := (fockPos _ _ (GlobalTheory.Branching.xiB_ne_zero (lamN lam) (sgN lam sg))).1
  have h3 := (fockPos _ _ (hwNe ℂ (n + 1) n (Nat.le_succ n) (lamN lam))).1
  have e : hw ℂ (Nat.le_succ n) (lamN lam) = map (algebraMap ℝ ℂ) (hw ℝ (Nat.le_succ n) (lamN lam)) :=
    (lclosedeq_hw_map _ _ _).symm
  rw [← map_xiB, fockF_map] at h1 h2
  rw [e, fockF_map] at h1 h3
  unfold Br.kapBr
  rw [xiBr_eq h, extremal_eq, fockB_incl, fockB_incl]
  exact ⟨div_pos h2 h3, (div_le_iff₀ h3).2 h1⟩

theorem spread_eq (lam : DomWeight (n + 1)) : lam.spread = lam.w 0 - lam.w (Fin.last n) + (n + 1 : ℕ) := by
  unfold DomWeight.spread
  rw [dif_pos (Nat.succ_pos n)]
  rfl

theorem kap_le (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    Br.kapBr ℝ rfl lam sg ≤ A ^ ((n + 1) * n / 2) := by
  have ha : Antitone (lamZ (lamN lam)) := fun a b hab => by
    have := lam.anti hab
    simp only [lamZ_lamN]
    omega
  refine (kap_bounds h).2.trans ((weylDimBound n _ ha).2.trans ?_)
  have h0 := ha (Fin.zero_le (Fin.last n))
  refine pow_le_pow_left₀ (add_nonneg (by exact_mod_cast sub_nonneg.2 h0) (Nat.cast_nonneg n)) ?_ _
  rw [spread_eq] at hA
  simp only [lamZ_lamN]
  push_cast at hA ⊢
  linarith

theorem cBr_eq (lam : DomWeight (n + 1)) (sg : DomWeight n) : Br.cBr rfl lam sg = cCap lam.w sg.w := by
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_
  ring

theorem c_bounds (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    Br.cBr rfl lam sg ≠ 0 ∧ |((Br.cBr rfl lam sg : ℤ) : ℝ)| ≤ A ^ (n * (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg).toNat) := by
  obtain ⟨h1, h2⟩ := capConst n lam.w sg.w (interlace_w h)
  rw [cBr_eq]
  refine ⟨h1, ?_⟩
  have e : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg = d1 lam.w sg.w := rfl
  rw [e]
  have h3 : |((cCap lam.w sg.w : ℤ) : ℝ)| ≤
      ((lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1 : ℤ) : ℝ) ^ (n * (d1 lam.w sg.w).toNat) := by exact_mod_cast h2
  refine h3.trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h0 := lam.anti (Fin.zero_le (Fin.last n))
  refine pow_le_pow_left₀ (by exact_mod_cast (by omega : (0 : ℤ) ≤ lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1)) ?_ _
  rw [spread_eq] at hA
  push_cast at hA ⊢
  linarith

theorem one_position (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    0 < ((Br.cBr rfl lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ rfl lam sg ∧
    Real.log (((Br.cBr rfl lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ rfl lam sg) ≤
      (2 * (((n + 1 : ℕ) : ℝ) - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg : ℤ) : ℝ) +
        ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) / 2) * Real.log A := by
  obtain ⟨c1, c2⟩ := c_bounds h hA
  have k1 := (kap_bounds h).1
  have k2 := kap_le h hA
  have c0 : ((Br.cBr rfl lam sg : ℤ) : ℝ) ≠ 0 := by exact_mod_cast c1
  have hd : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg := (interlaceIdent n lam.w sg.w (interlace_w h)).2.2.2.1
  have hd' : (((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg).toNat : ℕ) : ℝ) = ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg : ℤ) : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hd)
  have he : (((n + 1) * n / 2 : ℕ) : ℝ) = ((n : ℝ) + 1) * n / 2 := by
    rw [Nat.cast_div (by rw [mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd) (by norm_num)]
    push_cast
    ring
  refine ⟨by positivity, ?_⟩
  have l1 := Real.log_le_log (abs_pos.2 c0) c2
  have l2 := Real.log_le_log k1 k2
  rw [Real.log_pow, Real.log_abs, Nat.cast_mul, hd'] at l1
  rw [Real.log_pow, he] at l2
  rw [Real.log_mul (pow_ne_zero 2 c0) k1.ne', Real.log_pow]
  push_cast
  linarith

theorem orthNormLogBound : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.OrthNormLogBound := by
  refine ⟨2, fun ι _ N n hN lam sg h1 a ha => ?_⟩
  refine ⟨?_, ?_, GlobalTheory.BrNormCompare.last_ineq hN lam sg h1 a ha⟩
  · subst hN
    exact Finset.prod_pos fun τ _ => (one_position (h1 τ) (ha τ)).1
  · subst hN
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq
    rw [Real.log_prod fun τ _ => (one_position (h1 τ) (ha τ)).1.ne']
    exact Finset.sum_le_sum fun τ _ => (one_position (h1 τ) (ha τ)).2

end GlobalTheory.BranchLogBound
