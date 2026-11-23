import Formalism.LocalToGlobal.NormalizedHeckeFactors.RankZeroOfLevelThree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRowsEqRecordRows

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.L2.N.RankZeroOfLevelThree
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
open Formalism.L2.N.ExtNRows3 Formalism.L2.N.ExtNRows Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
theorem rank_zero_of_row_conditions_alt {eps : ℝ} (Fm : FamP eps) (x0 : ℝ)
    (T : ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.TiedDataSKAlt (Fm.ex x hx i))
    (P : ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, RowSideFamily (Fm.ex x hx i))
    (hp : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), _root_.Formalism.L2.Rows.RowSideDeterminedAlt (T x hx h0 i) (P x hx h0 i))
    (hL : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), RowsHoldLam3 (P x hx h0 i))
    (hR : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), Formalism.L2.DIV.DivRows3 (Fm.D x i) (P x hx h0 i).A3 (P x hx h0 i).P0
      (P x hx h0 i).ψ0 (P x hx h0 i).Ps (P x hx h0 i).ψs (P x hx h0 i).Zs (P x hx h0 i).S0 (P x hx h0 i).S1 (Fm.ex x hx i).p0
      (P x hx h0 i).C (P x hx h0 i).NuC (P x hx h0 i).I)
    (h : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), RowsHold0_3 (P x hx h0 i))
    (ht : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), ∃ t : (P x hx h0 i).T,
      (P x hx h0 i).I.tup t = (Fm.D x i).what₂.mu0 ∧
      ∀ k : Fin (Fm.D x i).R.m, Function.Surjective (lPrj (Fm.D x i) (P x hx h0 i).A3.A (P x hx h0 i).P0
        (P x hx h0 i).ψ0 ((P x hx h0 i).A3.fam3.toSub2 (P x hx h0 i).Zs) k t).mulVec) :
    SmallLevelRankEq Fm := by
  refine ⟨max x0 (Fm.x1 + 1), fun x hxx i j hj => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hxx)
  have h0 : x0 ≤ x := le_trans (le_max_left _ _) hxx
  obtain ⟨t, htup, hsurj⟩ := ht x hx1 h0 i
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨k, rfl⟩ : ∃ k : Fin (Fm.D x i).R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have key := (_root_.Formalism.L2.N.ExtNRows3.thetaT_injective_and_finrank_Zj_eq_D0_of_surjective (T x hx1 h0 i) (P x hx1 h0 i) (hp x hx1 h0 i) (hL x hx1 h0 i) (h x hx1 h0 i) (hR x hx1 h0 i) k t (hsurj k)).2
  rw [htup] at key
  exact key
end Formalism.L2.N.RankZeroOfLevelThree
end
end
