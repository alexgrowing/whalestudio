import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BTLeFiveQuarters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemTopPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WPlPos
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExcessMemIcc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRangeSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoWLeFirstRow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuDCardLeASq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankTwoLogbFiveSqLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XLeA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleOneLtA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlLeParams
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CapLe
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShapeRows

theorem ent_nu {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.nu u j z = nuD D u j z := by
  apply YoungDiagram.ext
  ext ⟨r, c⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen]
  have h : (E.nu u j z).rowLen r = (nuD D u j z).rowLen r := by
    have h1 := E.nu_row u j hj z r
    have h2 := nuRowOK D u j hj z r
    exact_mod_cast h1.trans h2.symm
  rw [h]

theorem ent_size {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.size u j z = (((nuD D u j z).card : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.size
  rw [ent_nu E u j hj z]

theorem ent_row {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) :
    E.row u j z r = (((nuD D u j z).rowLen r : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.row
  rw [ent_nu E u j hj z]

theorem ent_cap {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.cap u j z = if IsTopPl D z then (((nuD D u j z).rowLen 1 : ℕ) : ℝ) else (((nuD D u j z).rowLen 0 : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.cap
  rw [ent_row E u j hj z, ent_row E u j hj z]

theorem cap_le_width : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.LongRows.longRows Fm
  refine ⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩
  obtain ⟨-, hw, -⟩ := h1 x (le_trans (le_max_left _ _) hx) hx1 i j hj z
  have hr := h2 x (le_trans (le_max_right _ _) hx) hx1 i u j hj z
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    have := (Fm.D x i).R.two_le_m
    omega
  have hN : (Fm.D x i).R.k ≤ (Fm.D x i).R.N j := by unfold Ranks.N; omega
  have hS := (Fm.L x i).Sc_pos
  split_ifs with hz
  · have e := nuRowOK (Fm.D x i) u j hj z 1
    rw [if_pos (by omega)] at e
    have := ((hr 1 (by omega)).2 hz le_rfl (by omega)).2
    rw [e]
    linarith
  · have e := nuRowOK (Fm.D x i) u j hj z 0
    rw [if_pos (by omega)] at e
    have := ((hr 0 (by omega)).1 hz).2
    rw [if_pos rfl] at this
    rw [e]
    linarith

theorem shape : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (Ee : OrbitPlaces.Ent (Fm.D x i)), OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Ee := by
  intro eps Fm
  obtain ⟨a1, h1⟩ := GlobalTheory.Ggeo.wPl_pos Fm
  obtain ⟨a2, h2⟩ := GlobalTheory.ExcessLow.excess_mem_Icc Fm
  obtain ⟨a3, h3⟩ := GlobalTheory.TopExcess.top_excess Fm
  obtain ⟨a4, h4⟩ := GlobalTheory.TopFirstRow.two_w_le_first_row Fm
  obtain ⟨a5, h5⟩ := GlobalTheory.nuD_card_le_a_sq Fm
  obtain ⟨a6, h6⟩ := GlobalTheory.rank_two_logb_five_sq_le Fm
  obtain ⟨a7, h7⟩ := GlobalTheory.ShXa.X''_le_a Fm
  obtain ⟨a8, h8⟩ := GlobalTheory.family_one_lt_scale_a Fm
  obtain ⟨a9, h9⟩ := cap_le_width Fm
  obtain ⟨a10, h10⟩ := GlobalTheory.AlTop.al_le Fm
  obtain ⟨a11, h11⟩ := GlobalTheory.CapBound.cap_le Fm
  refine ⟨max a1 (max a2 (max a3 (max a4 (max a5 (max a6 (max a7 (max a8 (max a9 (max a10 a11))))))))),
    fun x hx hx1 i Ee => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hx
  exact
    { wpos := h1 x b1 hx1 i
      low := fun u j hj z hz => by
        rw [ent_size Ee u j hj z]
        exact h2 x b2 hx1 i u j hj z hz
      top := fun u j hj z hz => by
        rw [ent_size Ee u j hj z, ent_row Ee u j hj z]
        exact h3 x b3 hx1 i u j hj z hz
      top1 := fun u j hj z hz => by
        rw [ent_row Ee u j hj z]
        exact h4 x b4 hx1 i u j hj z hz
      sizeA := fun u j hj z => by
        rw [ent_size Ee u j hj z]
        exact h5 x b5 hx1 i u j hj z
      rankA := h6 x b6 hx1 i
      xa := ⟨h7 x b7 hx1 i, h8 x b8 hx1 i⟩
      capW := fun u j hj z => by
        rw [ent_cap Ee u j hj z]
        exact h9 x b9 hx1 i u j hj z
      alG := fun u j hj t ht => by
        rw [ent_row Ee u j hj, ent_row Ee u j hj]
        exact h10 x b10 hx1 i u j hj t ht
      capG := fun u j hj z => by
        rw [ent_cap Ee u j hj z]
        exact h11 x b11 hx1 i u j hj z }

end GlobalTheory.ShapeRows
