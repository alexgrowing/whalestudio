import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmBUse
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesPt

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.ThmBUseR

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.FourierDecayAlt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Stmt

variable (D : D7)

def JSqR {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist) (γ : Point D.host.E (D.R.rS + 1)) :
    ENNReal :=
  ∏ v, orbSq (X.L v) (X.f v) (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D v γ))

def BSumR {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (W : Point D.host.E (D.R.rS + 1) → ℝ) : ENNReal :=
  ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ},
    ENNReal.ofReal (wPt D γ.1 * ptWeightG D (rhoReal D) T T' γ.1.1 * W γ.1) * JSqR D X γ.1

def theoremBRotated (Aw Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    (∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
    BSumR D X (fun γ => normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

end Stmt

def JointNormBoundRotatedUniform : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, theoremBRotated D Aw Ch Cg Cb

section Core

variable {D : D7} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
  {Cl Nu : Type} (N : PN.NGData τ D.host.E D.R.rS Cl Nu)

def JointNormBoundRotated {Ch Cg : ℝ} {T T' : ℕ} {b : ℝ} (Bd : BData D Ch Cg T T' b 0) (Cj : ℝ) : Prop :=
  ∀ γ (w : Point D.host.E (D.R.rS + 1)), PN.IsPt X N γ → Formalism.L2.SG.RowsConc.toPts w = γ →
    Formalism.L2.SG.ThmBUse.IsRowPt D T T' w → ENNReal.ofReal (N.jacobianSquareBound γ) ≤ ENNReal.ofReal Cj * JSqR D Bd w

def TiesR (Ch Cg : ℝ) (T T' : ℕ) (b : ℝ) (A : ℕ) (Cb TB : ℝ) : Prop :=
  ∃ (Bd : BData D Ch Cg T T' b 0) (Cw Cj : ℝ), 0 ≤ Cw ∧ 0 ≤ Cj ∧
    (∀ v, AllGaps (Bd.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) ∧
    Formalism.L2.SG.ThmBUse.PtTie X N T T' ∧ Formalism.L2.SG.ThmBUse.WtTie X N T T' A Cw ∧ JointNormBoundRotated X N Bd Cj ∧
    Formalism.L2.SG.ThmBUse.NormTie Bd Cw Cj Cb TB

theorem pointSum_of_B3R {Ch Cg Cb : ℝ} {T T' A : ℕ} {b TB : ℝ} (hB3 : theoremBRotated D (A : ℝ) Ch Cg Cb)
    (hJ0 : ∀ γ, 0 ≤ N.jacobianSquareBound γ) (hTB : 0 ≤ TB) (h : TiesR X N Ch Cg T T' b A Cb TB) :
    PN.PointSumInput X N (A * (D.R.rS + 1) ^ 2) TB := by
  classical
  obtain ⟨Bd, Cw, Cj, hCw, hCj, hgap, hPt, hWt, hJ, hN⟩ := h
  intro S hS

  have hPt' : ∀ γ : S, ∃ w : Point D.host.E (D.R.rS + 1),
      Formalism.L2.SG.RowsConc.toPts w = γ.1 ∧ Formalism.L2.SG.ThmBUse.IsRowPt D T T' w :=
    fun γ => hPt γ.1 (hS γ.1 γ.2)
  choose w hw hwr using hPt'

  have key : ∀ γ : S, ENNReal.ofReal (Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ.1 * N.n γ.1 * (N.NG γ.1 * N.ND γ.1) ^ (A * (D.R.rS + 1) ^ 2) * N.jacobianSquareBound γ.1) ≤
      ENNReal.ofReal (Cw * Cj) * (ENNReal.ofReal (wPt D (w γ) * ptWeightG D (rhoReal D) T T' ((w γ)).1 *
              normWt D T T' (w γ) ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) * JSqR D Bd (w γ)) := by
    intro γ
    have hγ := hS γ.1 γ.2
    have h1 := hWt γ.1 (w γ) hγ (hw γ) (hwr γ)
    have h2 := hJ γ.1 (w γ) hγ (hw γ) (hwr γ)
    calc _ ≤ ENNReal.ofReal (Cw * (wPt D (w γ) * ptWeightG D (rhoReal D) T T' (w γ).1 *
              normWt D T T' (w γ) ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) * N.jacobianSquareBound γ.1) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h1 (hJ0 γ.1))
      _ = ENNReal.ofReal Cw * ENNReal.ofReal (wPt D (w γ) * ptWeightG D (rhoReal D) T T' ((w γ)).1 *
              normWt D T T' (w γ) ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) * ENNReal.ofReal (N.jacobianSquareBound γ.1) := by
          rw [ENNReal.ofReal_mul' (hJ0 γ.1), ENNReal.ofReal_mul hCw]
      _ ≤ ENNReal.ofReal Cw * ENNReal.ofReal (wPt D (w γ) * ptWeightG D (rhoReal D) T T' ((w γ)).1 *
              normWt D T T' (w γ) ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) * (ENNReal.ofReal Cj * JSqR D Bd (w γ)) := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul hCw]; ring

  have hinj : Function.Injective (fun γ : S =>
      (⟨w γ, (show IsBPt D T T' (w γ) ∧ _ from hwr γ).1⟩ :
        {p : Point D.host.E (D.R.rS + 1) // IsBPt D T T' p})) := by
    intro a b hab
    have hab' : w a = w b := congrArg Subtype.val hab
    apply Subtype.ext
    rw [← hw a, ← hw b, hab']
  have hpart : ∑' γ : S, ENNReal.ofReal (wPt D (w γ) * ptWeightG D (rhoReal D) T T' ((w γ)).1 *
              normWt D T T' (w γ) ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) * JSqR D Bd (w γ) ≤
      BSumR D Bd (fun γ => normWt D T T' γ ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) :=
    ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun p : {p : Point D.host.E (D.R.rS + 1) // IsBPt D T T' p} =>
        ENNReal.ofReal (wPt D p.1 * ptWeightG D (rhoReal D) T T' (p.1).1 *
              normWt D T T' p.1 ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) * JSqR D Bd p.1)
  have htot : ∑ γ : S, ENNReal.ofReal (Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ.1 * N.n γ.1 * (N.NG γ.1 * N.ND γ.1) ^ (A * (D.R.rS + 1) ^ 2) * N.jacobianSquareBound γ.1) ≤ ENNReal.ofReal TB :=
    calc _ ≤ ∑ γ : S, ENNReal.ofReal (Cw * Cj) * (ENNReal.ofReal (wPt D (w γ) * ptWeightG D (rhoReal D) T T' ((w γ)).1 *
              normWt D T T' (w γ) ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) * JSqR D Bd (w γ)) :=
          Finset.sum_le_sum fun γ _ => key γ
      _ = ENNReal.ofReal (Cw * Cj) * ∑' γ : S, ENNReal.ofReal (wPt D (w γ) * ptWeightG D (rhoReal D) T T' ((w γ)).1 *
              normWt D T T' (w γ) ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) * JSqR D Bd (w γ) := by
          rw [tsum_fintype, Finset.mul_sum]
      _ ≤ ENNReal.ofReal (Cw * Cj) *
          BSumR D Bd (fun γ => normWt D T T' γ ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) := by gcongr
      _ ≤ ENNReal.ofReal (Cw * Cj) *
          (ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) *
            Real.log b)) * jSqG D Bd) := by gcongr; exact hB3 T T' b Bd hgap
      _ ≤ ENNReal.ofReal TB := hN

  rw [← Finset.sum_coe_sort S]
  calc _ ≤ ∑ γ : S, (ENNReal.ofReal (Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ.1 * N.n γ.1 * (N.NG γ.1 * N.ND γ.1) ^ (A * (D.R.rS + 1) ^ 2) * N.jacobianSquareBound γ.1)).toReal :=
        Finset.sum_le_sum fun γ _ => by rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
    _ = (∑ γ : S, ENNReal.ofReal (Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ.1 * N.n γ.1 * (N.NG γ.1 * N.ND γ.1) ^ (A * (D.R.rS + 1) ^ 2) * N.jacobianSquareBound γ.1)).toReal :=
        (ENNReal.toReal_sum fun γ _ => ENNReal.ofReal_ne_top).symm
    _ ≤ (ENNReal.ofReal TB).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htot
    _ = TB := ENNReal.toReal_ofReal hTB

end Core

end Formalism.L2.SG.ThmBUseR
