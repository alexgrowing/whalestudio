import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.BlockSum

theorem detOn_prefix {n b : ℕ} {ε : Fin n → Bool} {W' : Flag n b}
    (hW : IsIsoFlag ε (fun _ => 1) W') {x : Fin b → ℝ} {t : UJ ε} (ht : IsSplit ε W' x t) (m : Fin (b + 1)) :
    detOn (uMat t) (W' m) = Real.exp (∑ l with l.castSucc < m, x l) := by
  induction m using Fin.induction with
  | zero => simp [hW.1, detOn_bot, Fin.not_lt_zero]
  | succ m ih =>
    rw [ht.detOn_succ hW m, ih, ← Real.exp_add]
    congr 1
    have e1 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.succ) = Iic m := by
      ext l; simp [Fin.castSucc_lt_succ_iff]
    have e2 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.castSucc) = Iio m := by
      ext l; simp
    rw [e1, e2, ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    simp [add_comm]

theorem blockSum_eq_zero : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a}
    {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) →
    (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) →
    ∀ {x : Fin b → ℝ} {t : UJ ε}, IsSplit ε W' x t → t ∈ leviOne ε W → ∀ i, ∑ l with β l = i, x l = 0 := by
  intro n a b ε W W' β p hW hp hβ x t ht hl i
  have hS : ∀ k : Fin (a + 1), ∑ l with l.castSucc < p k, x l = 0 := fun k => by
    have h1 := hl.2 k
    rw [← hp k, detOn_prefix hW ht] at h1
    exact Real.exp_eq_one_iff _ |>.1 h1
  set A := p i.castSucc
  set B := p i.succ
  have hblk : (Finset.univ.filter fun l : Fin b => β l = i) =
      ((Finset.univ.filter fun l : Fin b => l.castSucc < B).filter fun l => ¬ l.castSucc < A) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hβ, not_lt]; tauto
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun l : Fin b => l.castSucc < B) (fun l => l.castSucc < A) x
  rw [hS i.succ, ← hblk] at hsplit
  have h0 : ∑ l ∈ (Finset.univ.filter fun l : Fin b => l.castSucc < B).filter (fun l => l.castSucc < A), x l = 0 := by
    rw [Finset.filter_filter]
    rcases le_total A B with h | h
    · have : (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) =
          Finset.univ.filter fun l : Fin b => l.castSucc < A := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h' => h'.2, fun h' => ⟨lt_of_lt_of_le h' h, h'⟩⟩
      rw [this]; exact hS i.castSucc
    · have : (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) =
          Finset.univ.filter fun l : Fin b => l.castSucc < B := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h' => h'.1, fun h' => ⟨h', lt_of_lt_of_le h' h⟩⟩
      rw [this]; exact hS i.succ
  linarith

end GlobalTheory.RealInd.BlockSum
