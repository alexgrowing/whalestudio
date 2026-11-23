import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.KerJ NumberField Classical

noncomputable section

namespace GlobalTheory.KerWtStep

open Formalism.MainNotions.GL3Columns

theorem half_cast (R : Ranks) (j : ℕ) :
    (((j * (R.t + 1) / 2 : ℕ) : ℤ) : ℚ) = (j : ℚ) * ((R.t : ℚ) + 1) / 2 := by
  obtain ⟨c, hc⟩ := R.t_odd
  have h2 : j * (R.t + 1) = 2 * (j * (c + 1)) := by rw [hc]; ring
  rw [h2, Nat.mul_div_cancel_left _ two_pos]
  push_cast
  rw [hc]
  push_cast
  ring

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}

theorem lamTG_w (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (j : ℕ) (hj : j ≤ D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) : (((lamTG M j τ).w r : ℤ) : ℚ) = lamTr D u τ j r := by
  have h1 := M.lam_eq j hj τ r
  have h2 := lamNo_eq D u τ j r r.2
  show (((M.lam j τ).w r - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℤ) : ℚ) = _
  push_cast
  rw [h1]
  have h3 := half_cast D.R j
  push_cast at h3
  rw [h3]
  unfold lamNo at h2
  suffices e : (if h : r.1 < D.R.k then hcToWeightQ (D.hcW u τ).u ⟨r.1, h⟩
      else -wG D.R ((D.hcW u τ).e ⟨(r.1 - D.R.k) / (D.R.t + 1), D.R.blk_lt hj r h⟩) ((r.1 - D.R.k) / (D.R.t + 1) + 1)) =
      (if r.1 < D.R.k then lamZ D u τ r else -wJ D u τ ((r.1 - D.R.k) / (D.R.t + 1))) by
    rw [e, ← h2]; ring
  split_ifs with hk
  · simp only [hcToWeightQ, rhoVec, lamZ, dif_pos hk]
    push_cast
    ring
  · simp only [wJ, eJ, dif_pos (D.R.blk_lt hj r hk)]

theorem detShift_eq {N : ℕ} (l : DomWeight N) (hN : 0 < N) : l.detShift = l.w ⟨N - 1, by omega⟩ := dif_pos hN

theorem trueWt_step : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C)
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (i : ℕ), i < D.R.m →
    ∃ n : D.what₂.Tau → ℕ, (∀ τ r, (lamTG M i τ).natW r + n τ = nuT D u i τ r) ∧
      (∀ τ, (lamTG M i τ).detShift + C.sSharp i τ = n τ) ∧
      (∀ τ r, (lamTG M (i + 1) τ).natW r = extNu (D.R.N (i + 1)) (fun τ r => (lamTG M i τ).natW r + n τ) τ r) ∧
      ∀ τ, (lamTG M (i + 1) τ).detShift = -C.sDiv i τ := by
  intro D u C A Pm M i hi
  have hN := D.R.N_pos i
  have hlt : D.R.N i < D.R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  have hS : ∀ τ, (C.sSharp i τ : ℚ) = sJ' D u τ i := fun τ => ((wtRec_thm D u τ i hi).1 C).1
  have hD : ∀ τ, (C.sDiv i τ : ℚ) = sJ D u τ i := fun τ => ((wtRec_thm D u τ i hi).1 C).2
  have hnu : ∀ τ r, r < D.R.N i → DV.nuRow D u (i + 1) τ r = ((nuTr D u τ i r : ℚ) : ℝ) :=
    fun τ => (wtRec_thm D u τ i hi).2
  have wi := fun τ (r : Fin (D.R.N i)) => lamTG_w M i hi.le τ r
  have wi1 := fun τ (r : Fin (D.R.N (i + 1))) => lamTG_w M (i + 1) hi τ r
  have ds0 := fun τ => detShift_eq (lamTG M i τ) hN
  have ds1 := fun τ => detShift_eq (lamTG M (i + 1) τ) (D.R.N_pos (i + 1))
  have anti0 : ∀ τ (r : Fin (D.R.N i)), (lamTG M i τ).w ⟨D.R.N i - 1, by omega⟩ ≤ (lamTG M i τ).w r :=
    fun τ r => (lamTG M i τ).anti (show r ≤ ⟨D.R.N i - 1, by omega⟩ from Fin.le_def.2 (by simp; omega))
  have dq1 : ∀ τ, (((lamTG M (i + 1) τ).detShift : ℤ) : ℚ) = -sJ D u τ i := by
    intro τ
    rw [ds1, wi1]
    simp only [lamTr, if_neg (show ¬ (D.R.N (i + 1) - 1 < D.R.N i) by omega),
      if_pos (show D.R.N (i + 1) - 1 < D.R.N (i + 1) by omega)]
  have hpos : ∀ τ, 0 < (lamTG M i τ).detShift + C.sSharp i τ := by
    intro τ
    have h := RowWeightLemmas.nuRow_last_pos D u i hi τ
    rw [hnu τ _ (by omega)] at h
    have e : (((lamTG M i τ).detShift + C.sSharp i τ : ℤ) : ℚ) = nuTr D u τ i (D.R.N i - 1) := by
      rw [ds0]; push_cast; rw [wi, hS]; rfl
    have h' : (0 : ℚ) < nuTr D u τ i (D.R.N i - 1) := by exact_mod_cast h
    rw [← e] at h'
    exact_mod_cast h'
  refine ⟨fun τ => ((lamTG M i τ).detShift + C.sSharp i τ).toNat, ?_, ?_, ?_, ?_⟩
  · intro τ r
    have key : DV.nuRow D u (i + 1) τ r = ((((lamTG M i τ).w r + C.sSharp i τ : ℤ)) : ℝ) := by
      rw [hnu τ r r.2]
      have e : ((((lamTG M i τ).w r + C.sSharp i τ : ℤ)) : ℚ) = nuTr D u τ i r := by
        push_cast; rw [wi, hS]; rfl
      rw [← e, Rat.cast_intCast]
    unfold nuT
    rw [key, ← Int.floor_toNat, Int.floor_intCast]
    have a := anti0 τ r
    have d := ds0 τ
    have p := hpos τ
    unfold DomWeight.natW
    dsimp only
    omega
  · intro τ
    exact (Int.toNat_of_nonneg (hpos τ).le).symm
  · intro τ r
    unfold DomWeight.natW extNu
    by_cases h : r.1 < D.R.N i
    · rw [dif_pos h]
      have e : (lamTG M (i + 1) τ).w r - (lamTG M (i + 1) τ).detShift = (lamTG M i τ).w ⟨r.1, h⟩ + C.sSharp i τ := by
        have : (((lamTG M (i + 1) τ).w r - (lamTG M (i + 1) τ).detShift : ℤ) : ℚ) =
            (((lamTG M i τ).w ⟨r.1, h⟩ + C.sSharp i τ : ℤ) : ℚ) := by
          push_cast
          rw [wi1, dq1, wi, hS]
          simp only [lamTr, if_pos h]
          ring
        exact_mod_cast this
      rw [e]
      have a := anti0 τ ⟨r.1, h⟩
      have d := ds0 τ
      have p := hpos τ
      dsimp only
      omega
    · rw [dif_neg h]
      have e : (lamTG M (i + 1) τ).w r - (lamTG M (i + 1) τ).detShift = 0 := by
        have : (((lamTG M (i + 1) τ).w r - (lamTG M (i + 1) τ).detShift : ℤ) : ℚ) = ((0 : ℤ) : ℚ) := by
          push_cast
          rw [wi1, dq1]
          simp only [lamTr, if_neg h, if_pos r.2]
          ring
        exact_mod_cast this
      rw [e]
      rfl
  · intro τ
    have : (((lamTG M (i + 1) τ).detShift : ℤ) : ℚ) = ((-C.sDiv i τ : ℤ) : ℚ) := by
      push_cast; rw [dq1, hD]
    exact_mod_cast this

end GlobalTheory.KerWtStep
