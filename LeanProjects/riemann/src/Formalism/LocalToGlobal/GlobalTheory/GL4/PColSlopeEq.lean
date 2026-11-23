import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColSlope
import Formalism.LocalToGlobal.GlobalTheory.GL4.PNabla
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.UpperSlopeOfMaximalConstant

open Module NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree

def TSpanEqVV : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), TSpan K lam = VV K lam

def ZBasisStd : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), ∃ (Z : ZBasis lam) (μs : ι → ℝ), Nonempty Z.J0 ∧
    (∀ τ, MuStd (lam τ).natW (μs τ)) ∧ -Real.log (gramZ lam Z).det / (Fintype.card Z.J0 : ℝ) = ∑ τ, μs τ

def QSlope (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) c τ, (CV.Q c τ).mu = -Real.log (Tu D u) / D.R.k

theorem wsum_eq_colAbs (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ((wsum ((D.fm u).lam 0 τ) : ℤ) : ℝ) = colAbs D u τ := by
  have hk : D.R.N 0 = D.R.k := by simp only [Ranks.N]; omega
  rw [colAbs, wsum, Int.cast_sum]
  simp_rw [Formalism.MainNotions.flipTwoThree.weight_eq_lamCol]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((lamCol D u τ i : ℚ) : ℝ)) (D.R.N 0), hk]

theorem colSlopeEq_of (h1 : TSpanEqVV) (h2 : ZBasisStd) (D : D7) (h3 : QSlope D) : ColSlopeEq D := by
  intro u CV
  obtain ⟨Z, μs, hne, hμ, hdet⟩ := h2 D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)
  refine ⟨μs, hμ, ?_⟩
  haveI : Nonempty Z.J0 := hne
  haveI := CV.ne
  have hm := col_mu CV (h1 D.what₂.LL D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)) Z
  have key : ∑ c, ∑ τ, ((wsum ((D.fm u).lam 0 τ) * (Fintype.card Z.J0 : ℤ) : ℤ) : ℝ) * (CV.Q c τ).mu =
      ∑ _c : (D.mem u).C.cls 0, ∑ τ, colAbs D u τ * (Fintype.card Z.J0 : ℝ) *
        (-Real.log (Tu D u) / D.R.k) := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [h3 u CV c τ, ← wsum_eq_colAbs]
    push_cast
    ring
  have e2 : ∑ τ, colAbs D u τ * (Fintype.card Z.J0 : ℝ) * (-Real.log (Tu D u) / D.R.k) =
      -((Fintype.card Z.J0 : ℝ) * ∑ τ, colAbs D u τ / D.R.k * Real.log (Tu D u)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  rw [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, e2] at hm
  have hN : (0 : ℝ) < Fintype.card Z.J0 := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < Fintype.card ((D.mem u).C.cls 0) := by exact_mod_cast Fintype.card_pos
  rw [← hdet]
  apply mul_left_cancel₀ (mul_ne_zero hN.ne' hC.ne')
  have hN' : (Fintype.card Z.J0 : ℝ) ≠ 0 := hN.ne'
  have e3 : (Fintype.card Z.J0 : ℝ) * Fintype.card ((D.mem u).C.cls 0) *
      (-Real.log (gramZ ((D.fm u).lam 0) Z).det / Fintype.card Z.J0) =
      -(Fintype.card ((D.mem u).C.cls 0) * Real.log (gramZ ((D.fm u).lam 0) Z).det) := by
    field_simp
  rw [hm, mul_add, e3]
  ring

theorem Link5F_of_three (h1 : TSpanEqVV) (h2 : ZBasisStd) (h3 : ∀ D, QSlope D) : Link5F := by
  unfold Link5F
  intro eps Fm _ _ _
  exact Formalism.MainNotions.flipTwoThree.familySlopeLower_of_open Fm
    ⟨0, fun x _ _ i => Formalism.MainNotions.flipTwoThree.lower_slope_of_column_slope _ (colSlopeEq_of h1 h2 _ (h3 _))⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
