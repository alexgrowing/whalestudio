import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.OnePDecay

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing

theorem hsn_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : hsn A = ‖A‖ := by
  rw [hsn, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (Real.rpow_natCast _ 2).symm

theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : hsn (A * B) ≤ hsn A * hsn B := by
  rw [hsn_eq_norm, hsn_eq_norm, hsn_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Frob

theorem hsn_nonneg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn A := Real.sqrt_nonneg _

theorem continuous_hsn_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun s : ℝ => hsn (NormedSpace.exp (s • X) : Matrix (Fin n) (Fin n) ℂ) := by
  unfold hsn
  refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)
  exact (continuous_iff_continuousAt.2 fun t => (GlobalTheory.Mem.Lift.hasDerivAt_exp_entry X t i j).continuousAt).norm.pow 2

theorem decay_oneP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ N : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (x : GA D V) (t : ℝ), |t| < 1 → ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤
        L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ := by
  intro D θ hθ V τ X hX N
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_hsn_exp X).continuousOn
  set m : ℝ := max 1 (max M (hsn (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hbound : ∀ τ' (s : ℝ), |s| ≤ 1 → hsn (cmp θ τ' (oneP θ V τ X s)) ≤ m := by
    intro τ' s hs
    have h := GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s
    by_cases e : τ' = τ
    · subst e
      show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.1]
      have := hM s ⟨(abs_le.1 hs).1, (abs_le.1 hs).2⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_of_le_right (le_max_left _ _)))
    · show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.2 τ' e]
      exact le_max_of_le_right (le_max_right _ _)
  have hkey : ∀ (x : GA D V) (t : ℝ) τ', |t| < 1 →
      1 + hsn (cmp θ τ' x) ≤ (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) * m := by
    intro x t τ' ht
    have hx : x = x * oneP θ V τ X t * oneP θ V τ X (-t) := by
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one]
    have h1 : hsn (cmp θ τ' x) ≤ hsn (cmp θ τ' (x * oneP θ V τ X t)) * m := by
      have e2 : cmp θ τ' x = cmp θ τ' (x * oneP θ V τ X t) * cmp θ τ' (oneP θ V τ X (-t)) := by
        show infMat _ _ (θ τ') x = infMat _ _ (θ τ') _ * infMat _ _ (θ τ') _
        rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, ← hx]
      rw [e2]
      exact (hsn_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (hbound τ' (-t) (by rw [abs_neg]; exact ht.le)) (hsn_nonneg' _))
    nlinarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]
  refine ⟨m ^ (N * Fintype.card D.what₂.Tau), by positivity, fun x t ht => ?_⟩
  rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun τ' _ => inv_nonneg.2 (pow_nonneg (by linarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]) N)) (fun τ' _ => ?_)
  have ha := hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))
  have hb := hsn_nonneg' (cmp θ τ' x)
  have hk := hkey x t τ' ht
  have hpa : 0 < (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N := pow_pos (by linarith) N
  have hpb : 0 < (1 + hsn (cmp θ τ' x)) ^ N := pow_pos (by linarith) N
  rw [← div_eq_mul_inv, le_div_iff₀ hpb, inv_mul_eq_div, ← div_pow]
  refine pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) ?_ N
  rw [div_le_iff₀ (by linarith)]
  linarith

end GlobalTheory.OnePDecay

end
