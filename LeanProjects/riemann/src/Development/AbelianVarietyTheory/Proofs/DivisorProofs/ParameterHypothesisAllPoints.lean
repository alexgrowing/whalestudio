import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

theorem parOf_hyp : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Hyp := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ j => ?_⟩⟩⟩
  have P := Fm.params x hx i
  have hrk := (Fm.D x i).sp.V_rank ((j : ℕ) + 1) (Nat.le_add_left _ _) j.2
  have h2 := (Fm.D x i).R.two_le_m
  have h3 := (Fm.D x i).R.m_add_three_le_k
  have h5 := (Fm.D x i).R.rank_add_five_le
  have h6 := (Fm.D x i).R.three_m_lt_t
  have hlst : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.lstar (parOf (Fm.L x i) j) = Formalism.BasicNotions.LevelStarExponents.lStar (Fm.L x i) := by
    simp only [Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.lstar, Formalism.BasicNotions.LevelStarExponents.lStar, Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.N, Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.b, parOf,
      Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Scale.b]
    push_cast
    ring
  have hb : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.b (parOf (Fm.L x i) j) = (Fm.L x i).sc.b := rfl
  refine
    { x_ge := (Fm.L x i).sc.one_lt_alt.le
      b'_pos := (Fm.L x i).sc.b'_pos
      m_pos := by show 1 ≤ (Fm.D x i).R.m; omega
      n_pos := (Fm.D x i).R.ord_pos
      f_pos := by show 1 ≤ 2 * (Fm.D x i).R.ord; have := (Fm.D x i).R.ord_pos; omega
      t_ge := by show (Fm.D x i).R.k + (Fm.D x i).R.m + 4 ≤ (Fm.D x i).R.t; omega
      t_gt := h6
      m_le := by show (Fm.D x i).R.m ≤ (Fm.D x i).R.k; omega
      η_le := by rw [hb]; exact P.eta_le
      Nr_eq := by
        show (Vc (Fm.D x i) j).rank + 1 = (Fm.D x i).R.k + (Fm.D x i).R.m + (Fm.D x i).R.t
        rw [hrk]
        show (Fm.D x i).R.k + (Fm.D x i).R.m - 1 + (Fm.D x i).R.t + 1 = (Fm.D x i).R.k + (Fm.D x i).R.m + (Fm.D x i).R.t
        omega
      t_le := P.t_le_eta
      S_nonneg := (Fm.L x i).Sc_pos.le
      sum_lt := by rw [hlst, hb]; exact P.lstar1
      win_lt := by rw [hlst, hb]; exact P.lstar2 }

end GlobalTheory.ExpTie
