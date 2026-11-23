import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValue
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightPolynomialDivDetPowEqPolyOfBlockMatricesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem sgRev_mul_self_eq_one (n : ℕ) : sgRev n * sgRev n = 1 := by
  unfold sgRev
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> rw [h] <;> norm_num

theorem sgRev_ne_zero_of_sq (n : ℕ) : sgRev n ≠ 0 := fun h => by simpa [h] using sgRev_mul_self_eq_one n

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem det_zT_of_odd {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (ho : IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = sgRev n * ((f τ).det)⁻¹ := by
  unfold zT
  rw [if_pos ho]
  have : (((f τ)⁻¹).transpose.submatrix id Fin.rev) = (((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n))) := rfl
  rw [this, Matrix.det_permute', Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rfl

theorem det_zT_of_even {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (ho : ¬ IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = (f τ).det := by
  unfold zT
  rw [if_neg ho]

def frVarToModel (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (k : GL3Theta.FrV D n) : Var (X.Pj i) :=
  ⟨((posJ X D pos i).symm k.1).1, ((posJ X D pos i).symm k.1).2, (Fin.cast h.symm k.2.1, Fin.cast h.symm k.2.2)⟩

theorem valZ_rename_frVar (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R0 : MvPolynomial (GL3Theta.FrV D n) ℂ)
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    valZ X D pos i h (MvPolynomial.rename (frVarToModel X D pos i h) R0) f = GL3Theta.evFr D R0 (zT X D pos f) := by
  unfold valZ GL3Theta.evFr
  rw [MvPolynomial.eval_rename]
  congr 2
  funext k
  simp [frVarToModel]

end GlobalTheory.TwV.DelA
end

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem realises_of_wtPol : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) {n : ℕ} (h : (X.Pj (j + 1)).m + 1 = n) (ν : D.what₂.Tau → Fin n → ℕ), (∀ τ r, (ν τ r : ℤ) ≤ cT1 X D pos j τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ R, Realises X D pos (j + 1) h (wT X D pos j) Q R := by
  intro p _ X D pos j n h ν hν Q hQ
  obtain ⟨R0, hR0⟩ := GlobalTheory.T.weightPolynomial_div_detPow_eq_poly_of_blockMatrices X D pos ν (cT1 X D pos j) hν Q hQ
  refine ⟨(∏ τ, if IsOddPos (pos.symm τ).2 then sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ)) else 1) •
    MvPolynomial.rename (frVarToModel X D pos (j + 1) h) R0, ?_⟩
  intro f
  have hd : ∀ τ, (f.1 τ).det ≠ 0 := fun τ => (f.2 τ).ne_zero
  have hv := valZ_rename_frVar X D pos (j + 1) h R0 f.1
  unfold valZ at hv
  rw [ev1_eq_prod_det_pow_mul_valZ]
  unfold valZ
  rw [MvPolynomial.smul_eval, hv, hR0 f.1 hd]
  have key : (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos (j + 1) τ) *
      (∏ τ, if IsOddPos (pos.symm τ).2 then sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ)) else 1) *
      (∏ τ, if IsOddPos (pos.symm τ).2 then (f.1 τ).det ^ (-(cT1 X D pos j τ)) else 1) =
      ∏ τ, (f.1 τ).det ^ (-(wT X D pos j τ)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [(GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j τ).2]
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [if_pos ho]
      rw [det_zT_of_odd X D pos f.1 τ ho, mul_zpow, inv_zpow']
      have hs : sgRev n ^ (wT X D pos j τ - cT1 X D pos j τ) * sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ)) = 1 := by
        rw [← zpow_add₀ (sgRev_ne_zero_of_sq n), add_neg_cancel, zpow_zero]
      have hdd : (f.1 τ).det ^ (-(wT X D pos j τ - cT1 X D pos j τ)) * (f.1 τ).det ^ (-(cT1 X D pos j τ)) =
          (f.1 τ).det ^ (-(wT X D pos j τ)) := by
        rw [← zpow_add₀ (hd τ)]; congr 1; ring
      calc _ = (sgRev n ^ (wT X D pos j τ - cT1 X D pos j τ) * sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ))) *
            ((f.1 τ).det ^ (-(wT X D pos j τ - cT1 X D pos j τ)) * (f.1 τ).det ^ (-(cT1 X D pos j τ))) := by ring
        _ = _ := by rw [hs, hdd, one_mul]
    · simp only [if_neg ho, mul_one]
      rw [det_zT_of_even X D pos f.1 τ ho]
  rw [← key]
  ring

end GlobalTheory.TwV.DelA
end
