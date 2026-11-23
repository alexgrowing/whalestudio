import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPhiA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem single_mul_single_one (i j k l : Fin n) :
    Matrix.single i j (1 : ℂ) * Matrix.single k l 1 = if j = k then Matrix.single i l 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

theorem lhol_neg (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (z : Matrix (Fin n) (Fin n) ℂ) : Lhol (-X) F z = -Lhol X F z := by
  simp [Lhol, Matrix.neg_mul]

theorem phiM_contDiffOn (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (PhiM μ) (OmegaSet n) :=
  fun _ hz => (contDiffAt_phiM μ hz).contDiffWithinAt

def phiT (μ : Fin n → ℤ) : smoothS n :=
  ⟨(OmegaSet n).indicator (PhiM μ), (phiM_contDiffOn μ).congr fun _ hz => Set.indicator_of_mem hz _⟩

theorem phiT_eqOn (μ : Fin n → ℤ) :
    Set.EqOn (PhiM μ) ((phiT μ : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n) :=
  fun _ hz => (Set.indicator_of_mem hz _).symm

theorem eOp_phiT (μ : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (h : ∀ z ∈ OmegaSet n, Lhol X (PhiM μ) z = c * PhiM μ z) : eOp X (phiT μ) = c • phiT μ := by
  apply Subtype.ext
  funext z
  rw [eOp_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, lhol_congr (phiT_eqOn μ).symm hz, h z hz, ← phiT_eqOn μ hz]
  · rw [ltOp_of_not_mem _ hz]
    simp [phiT, Set.indicator_apply, hz]

def xRev (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
  fun a b => -Matrix.single (Fin.rev a) (Fin.rev b) 1

def xTr (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
  fun a b => Matrix.single b a 1

theorem xRev_rel (a b c d : Fin n) : xRev n c d * xRev n a b - xRev n a b * xRev n c d =
    (if b = c then xRev n a d else 0) - (if d = a then xRev n c b else 0) := by
  unfold xRev
  rw [neg_mul_neg, neg_mul_neg, single_mul_single_one, single_mul_single_one]
  by_cases h1 : b = c
  · subst h1
    by_cases h2 : d = a
    · subst h2
      simp <;> abel
    · simp [h2, Ne.symm h2]
  · by_cases h2 : d = a
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem xTr_rel (a b c d : Fin n) : xTr n c d * xTr n a b - xTr n a b * xTr n c d =
    (if b = c then xTr n a d else 0) - (if d = a then xTr n c b else 0) := by
  unfold xTr
  rw [single_mul_single_one, single_mul_single_one]
  by_cases h1 : b = c
  · subst h1
    by_cases h2 : d = a
    · subst h2
      simp <;> abel
    · simp [h2, Ne.symm h2]
  · by_cases h2 : d = a
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem hw_rev (μ : Fin n → ℤ) :
    IsHWVec (fun a b => eOp (xRev n a b)) (fun a => ((μ (Fin.rev a) : ℤ) : ℝ)) (phiT μ) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine eOp_phiT μ _ _ fun z hz => ?_
    unfold xRev
    rw [lhol_neg, lhol_phiM_diag μ _ hz]
    push_cast
    ring
  · have h0 : eOp (xRev n a b) (phiT μ) = (0 : ℂ) • phiT μ := by
      refine eOp_phiT μ _ _ fun z hz => ?_
      unfold xRev
      rw [lhol_neg, lhol_phiM_lower μ (Fin.rev_lt_rev.2 hab) hz]
      simp
    rw [h0, zero_smul]

theorem hw_tr (μ : Fin n → ℤ) :
    IsHWVec (fun a b => eOp (xTr n a b)) (fun a => -((μ a : ℤ) : ℝ)) (phiT μ) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine eOp_phiT μ _ _ fun z hz => ?_
    unfold xTr
    rw [lhol_phiM_diag μ _ hz]
    push_cast
    ring
  · have h0 : eOp (xTr n a b) (phiT μ) = (0 : ℂ) • phiT μ := by
      refine eOp_phiT μ _ _ fun z hz => ?_
      unfold xTr
      rw [lhol_phiM_lower μ hab hz]
      simp
    rw [h0, zero_smul]

theorem rho_rev_add (a : Fin n) : rho n (Fin.rev a) + rho n a = 0 := by
  have ha := a.isLt
  unfold rho
  rw [Fin.val_rev, Nat.cast_sub (by omega : a.val + 1 ≤ n)]
  push_cast
  ring

private theorem gval_comp_perm (l : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    gval (fun r => l (σ r)) k = gval l k := by
  have h : (∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l (σ r)) * PowerSeries.X)⁻¹)) =
      ∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹) :=
    Equiv.prod_comp σ (fun r => 1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹)
  unfold gval gelfandSeries
  beta_reduce
  rw [h]

theorem gelfand_phiM (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) (k : ℕ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    opGelfand (fun a b => Lhol (Matrix.single a b (1 : ℂ))) k (PhiM μ) z =
        ((-1 : ℂ) ^ k * gval (icShift lam) k) * PhiM μ z ∧
      opGelfand (fun a b => Lhol (Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ))) k (PhiM μ) z =
        gval (icShift (-lam)) k * PhiM μ z := by
  constructor
  · have hY : ∀ a b, Matrix.single a b (1 : ℂ) = (-1 : ℂ) • xRev n (Fin.revPerm a) (Fin.revPerm b) := by
      intro a b
      simp [xRev]
    have hν : ((fun a => ((μ (Fin.rev a) : ℤ) : ℝ)) + rho n) = fun a => lam (Fin.revPerm a) := by
      funext a
      simp only [Pi.add_apply, Fin.revPerm_apply, hμ (Fin.rev a)]
      have := rho_rev_add (n := n) a
      linarith
    refine (opGelfand_eq (xRev n) _ Fin.revPerm (-1) hY (PhiM μ) (phiT μ) (phiT_eqOn μ) k hz).trans ?_
    rw [gelfand_hw (isGlRep_eOp (xRev n) xRev_rel) (hw_rev μ) k, hν, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← phiT_eqOn μ hz]
    rw [show icShift (fun a => lam (Fin.revPerm a)) = fun a => icShift lam (Fin.revPerm a) from rfl,
      gval_comp_perm]
    ring
  · have hY : ∀ a b, Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ) =
        (1 : ℂ) • xTr n (Fin.revPerm a) (Fin.revPerm b) := by
      intro a b
      simp [xTr]
    have hν : ((fun a => -((μ a : ℤ) : ℝ)) + rho n) = -lam := by
      funext a
      simp only [Pi.add_apply, Pi.neg_apply, hμ a]
      ring
    refine (opGelfand_eq (xTr n) _ Fin.revPerm 1 hY (PhiM μ) (phiT μ) (phiT_eqOn μ) k hz).trans ?_
    rw [gelfand_hw (isGlRep_eOp (xTr n) xTr_rel) (hw_tr μ) k, hν, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← phiT_eqOn μ hz, one_pow, one_mul]

end ReciprocityTheory.ChartRestriction.DS.S7
