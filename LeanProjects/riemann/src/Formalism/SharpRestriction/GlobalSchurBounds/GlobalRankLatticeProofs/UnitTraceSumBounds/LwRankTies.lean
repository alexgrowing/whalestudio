import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CountHypothesesIffText
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLz

noncomputable section

namespace Formalism.MainNotions.Ext.Lw

open Formalism.BasicNotions Formalism.MainNotions

theorem splitsF_g_all (D : D7) : ∀ j, StandardLattice.SplitsF D (D.host.g j) := fun j => J.splitsF_g D j

theorem splitsF_T_all (D : D7) (u : D.what₂.Word) : StandardLattice.SplitsF D (D.mem u).A.T := J.level_prime_splits_totally_real D u

theorem rank_conditions_iff_lowest_space {eps : ℝ} (Fm : FamP eps) :
    RankTiesF Fm ↔ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u := by
  unfold RankTiesF
  constructor
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i u => ((hx0 x hx i).2 u).2⟩
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i => ⟨splitsF_g_all (Fm.D x i), fun u => ⟨splitsF_T_all (Fm.D x i) u, hx0 x hx i u⟩⟩⟩

theorem rank_conditions_of_lowest_space {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u) : RankTiesF Fm :=
  (rank_conditions_iff_lowest_space Fm).2 h

theorem rankTiesF_of_col {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      StandardLattice.adm17 (Fm.D x i) (Fm.ex x hx i).lev ∧ StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev ∧ StandardLattice.AdmittedWeylDimension (Fm.D x i) ∧
        ∀ u : (Fm.D x i).what₂.Word, ∃ X : StandardLattice.ColRep (Fm.D x i) (Fm.ex x hx i).lev u,
          StandardLattice.BaseWeightColumnCondition (Fm.D x i) (Fm.ex x hx i).lev u X) :
    RankTiesF Fm := by
  obtain ⟨x0, h⟩ := h
  refine rank_conditions_of_lowest_space Fm ⟨max x0 (max 3 (Fm.x1 + 1)), fun x hx i u => ?_⟩
  have e0 : x0 ≤ x := (le_max_left _ _).trans hx
  have e3 : 3 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have e1 : Fm.x1 < x := by
    have := ((le_max_right 3 (Fm.x1 + 1)).trans (le_max_right x0 _)).trans hx
    linarith
  obtain ⟨h17, hp, hW, hX⟩ := h x e1 e0 i
  obtain ⟨X, hX⟩ := hX u
  exact StandardLattice.mu0Tie_of_col (Fm.D x i) (Fm.ex x e1 i).lev h17 hp (GlobalTheoryTheory.JDB.gBig_fam Fm x e3 e1 i) hW u X hX

end Formalism.MainNotions.Ext.Lw

end
