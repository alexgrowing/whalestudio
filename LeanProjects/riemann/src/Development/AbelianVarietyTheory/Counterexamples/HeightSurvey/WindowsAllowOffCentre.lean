import Mathlib
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

noncomputable section

namespace GlobalTheory.RunCounterexample

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {Q : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem last_plus (hK : DV.KapDef D) (hn : Even D.R.nV) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (hi : i.1 + 1 = (D.R.sigW j).1) :
    (((Cons.kaWt D hK hn j).aP τ i : ℕ) : ℝ) =
      ((((D.hc τ).e ⟨j - 1, by omega⟩ - (D.hc τ).b ⟨j - 1, by omega⟩ : ℚ)) : ℝ) - ((D.R.t : ℝ) + 1) / 2 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hi' : i.1 + 1 = D.R.k + j - 1 := hi
  have e1 := Cons.kaWt_big D hK hn j h1 h2 τ i
  have e2 := (hK j h1 h2 τ).1 i
  have hlt : ¬ (i.1 < D.R.k - 1) := by omega
  have hb : i.1 - (D.R.k - 1) < D.R.m := by omega
  have hc : ((i.1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1 := by
    have : i.1 + 2 = D.R.k + j := by omega
    have h' : ((i.1 : ℚ) + 2) = D.R.k + j := by exact_mod_cast this
    linarith
  rw [DV.aPlusQ_eq, hc] at e2
  unfold DV.sigPar DV.eQ at e2
  rw [dif_neg hlt, dif_pos hb, dif_pos ⟨h1, h2⟩] at e2
  have hx : (⟨i.1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ := Fin.ext (by show i.1 - (D.R.k - 1) = j - 1; omega)
  rw [hx, ← e1] at e2
  have e3 : (((Cons.kaWt D hK hn j).aP τ i : ℕ) : ℚ) =
      ((D.hc τ).e ⟨j - 1, by omega⟩ - (D.hc τ).b ⟨j - 1, by omega⟩ : ℚ) - ((D.R.t : ℚ) + 1) / 2 := by
    push_cast at e2; linarith
  have e4 := congrArg (fun q : ℚ => (q : ℝ)) e3
  push_cast at e4 ⊢
  exact e4

theorem last_minus (hK : DV.KapDef D) (hn : Even D.R.nV) (h1 : 1 ≤ j) (h2 : j < D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).2) (hi : i.1 + 1 = (D.R.sigW j).2) :
    (((Cons.kaWt D hK hn j).aM τ i : ℕ) : ℝ) =
      ((((D.hc τ).b ⟨j, h2⟩ - (D.hc τ).e ⟨j - 1, by omega⟩ : ℚ)) : ℝ) - ((D.R.t : ℝ) + 1) / 2 := by
  have e1 := Cons.kaWt_small D hK hn j h1 h2.le τ i
  have e2 := (hK j h1 h2.le τ).2 (Fin.rev i)
  have h0 : ((Fin.rev i : Fin _) : ℕ) = 0 := by rw [Fin.val_rev]; omega
  rw [h0] at e2
  unfold DV.aMinusQ DV.eQ at e2
  rw [dif_pos (by omega : j + 0 < D.R.m), dif_pos ⟨h1, h2.le⟩] at e2
  have e1' : (((Cons.kaWt D hK hn j).aM τ i : ℕ) : ℚ) = -(D.what₂.kaSmall j τ (Fin.rev i) : ℚ) := by exact_mod_cast e1
  have e3 : (((Cons.kaWt D hK hn j).aM τ i : ℕ) : ℚ) =
      ((D.hc τ).b ⟨j, h2⟩ - (D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) - ((D.R.t : ℚ) + 1) / 2 := by
    rw [e1', e2]; simp
  have e4 := congrArg (fun q : ℚ => (q : ℝ)) e3
  push_cast at e4 ⊢
  exact e4

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem clauses_at_shifted_gap (T : ParamsT D L P) (hK : DV.KapDef D) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    4 * (T.TO : ℝ) ^ 2 + D.R.t + 1 ≤ LevelStarExponents.h0 L - 4 ∧
    (∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      (LevelStarExponents.h0 L - 4) / 2 - ((D.R.t : ℝ) + 1) / 2 ≤ ((Cons.kaR T hK j).aP τ i : ℝ)) ∧
    (∀ τ (i : Fin (D.R.sigW j).2), i.1 + 1 = (D.R.sigW j).2 →
      (LevelStarExponents.h0 L - 4) / 2 - ((D.R.t : ℝ) + 1) / 2 ≤ ((Cons.kaR T hK j).aM τ i : ℝ)) := by
  have ht : (5 : ℝ) ≤ D.R.t := by
    have := D.R.rank_add_five_le
    exact_mod_cast (by omega : 5 ≤ D.R.t)
  refine ⟨by have := T.heightBound_ge_order_sq; linarith, fun τ i hi => ?_, fun τ i hi => ?_⟩
  · have hc := abs_le.1 (P.e_centred τ ⟨j - 1, by omega⟩)
    unfold Cons.kaR
    rw [last_plus hK _ h1 h2 τ i hi]
    linarith [hc.1]
  · have h3 : j < D.R.m := by
      have hs : (D.R.sigW j).2 = D.R.m - j := rfl
      omega
    have hc := abs_le.1 (P.e_centred τ ⟨j - 1, by omega⟩)
    have hg := (P.nodes_gap τ (j - 1) (by omega)).1
    have hx : (⟨j - 1 + 1, by omega⟩ : Fin D.R.m) = ⟨j, h3⟩ := Fin.ext (by show j - 1 + 1 = j; omega)
    rw [hx] at hg
    unfold Cons.kaR
    rw [last_minus hK _ h1 h3 τ i hi]
    push_cast at hc hg ⊢
    linarith [hc.2]

end GlobalTheory.RunCounterexample
