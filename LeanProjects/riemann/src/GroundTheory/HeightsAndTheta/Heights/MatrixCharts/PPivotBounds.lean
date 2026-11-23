import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PivotBounds

theorem qf_submatrix_castLE {d m : ℕ} (h : m ≤ d) (S : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin m → ℝ) :
    MCSchur.qf (S.submatrix (Fin.castLE h) (Fin.castLE h)) x =
      MCSchur.qf S (Function.extend (Fin.castLE h) x 0) := by
  have hinj : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  set y := Function.extend (Fin.castLE h) x 0 with hy
  have hyc : ∀ a, y (Fin.castLE h a) = x a := fun a => hinj.extend_apply x 0 a
  have hy0 : ∀ b ∉ Set.range (Fin.castLE h), y b = 0 := by
    intro b hb
    rw [hy, Function.extend_apply' _ _ _ (by rintro ⟨a, rfl⟩; exact hb ⟨a, rfl⟩)]
    rfl
  unfold MCSchur.qf
  simp only [dotProduct, mulVec]
  refine Fintype.sum_of_injective _ hinj _ _ (fun b hb => by rw [hy0 b hb, zero_mul]) ?_
  intro a
  rw [hyc]
  congr 1
  refine Fintype.sum_of_injective _ hinj _ _ (fun b hb => by rw [hy0 b hb, mul_zero]) ?_
  intro b
  rw [hyc]
  rfl

end PivotBounds

theorem PivotBounds.proof (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement)
    (hPI : PivotInvDiag.Statement) (hPL : PivotLast.Statement) : PivotBounds.Statement := by
  intro d S hS i
  have h : (i : ℕ) + 1 ≤ d := i.isLt
  set L := S.submatrix (Fin.castLE h) (Fin.castLE h) with hLdef
  have hL : L.PosDef := hS.submatrix (Fin.castLE_injective h)
  have hpiv : pivot L i = pivot S i := by
    unfold pivot
    rw [hLL d S _ h _ le_rfl, hLL d S _ h _ (Nat.le_succ _)]
  have hlast : Fin.castLE h (Fin.last (i : ℕ)) = i := Fin.ext rfl
  refine ⟨?_, ?_⟩
  · have h1 := hPL i L hL (Pi.single (Fin.last (i : ℕ)) 1)
    rw [hpiv] at h1
    have hq : MCSchur.qf L (Pi.single (Fin.last (i : ℕ)) 1) = S i i := by
      unfold MCSchur.qf
      rw [mulVec_single_one, single_one_dotProduct]
      simp [hLdef, hlast]
    simpa [hq] using h1
  · intro ε hε hy
    have hx : ∀ x : Fin ((i : ℕ) + 1) → ℝ, ε * x (Fin.last (i : ℕ)) ^ 2 ≤ MCSchur.qf L x := by
      intro x
      have := hy (Function.extend (Fin.castLE h) x 0)
      have he := (Fin.castLE_injective h).extend_apply x (0 : Fin d → ℝ) (Fin.last (i : ℕ))
      rw [hlast] at he
      rwa [he, ← PivotBounds.qf_submatrix_castLE] at this
    have hinv := MCCusp.inv_diag_le hL (Fin.last (i : ℕ)) hε hx
    have hone := hPI i L hL
    have hpos : 0 < L⁻¹ (Fin.last (i : ℕ)) (Fin.last (i : ℕ)) := hL.inv.diag_pos
    rw [hpiv] at hone
    set a := L⁻¹ (Fin.last (i : ℕ)) (Fin.last (i : ℕ))
    have hεa : ε * a ≤ 1 := by
      rw [le_div_iff₀ hε] at hinv
      linarith
    have hp : 0 < pivot S i := by
      by_contra hc
      have hc' := not_lt.mp hc
      nlinarith
    nlinarith

end

end GroundTheory.Heights₂.Heights
