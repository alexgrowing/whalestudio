import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HkLatTupUpdate

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def nC (v : X.Pl) (i l : ℕ) : ℕ :=
  (p ^ X.G.P.n' v) ^ ((i - l) * (X.t + 1 - l)) * Formalism.G0.gaussBinom (p ^ X.G.P.n' v) (X.t + 1) l

theorem latAt_succ_upd (v : X.Pl) (j : ℕ) (L' : (X.Pj (j + 1)).Tup)
    (L1 : Submodule ((X.Pj (j + 1)).W (X.vJ (j + 1) v)) (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq (X.vJ (j + 1) v))) :
    X.latAt v (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = L1 :=
  Function.update_self (β := fun u => Submodule ((X.Pj (j + 1)).W u) (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq u))
    (X.vJ (j + 1) v) L1 L'

theorem latAt_zero_upd (v : X.Pl) (L' : (X.Pj 0).Tup)
    (L1 : Submodule ((X.Pj 0).W (X.vJ 0 v)) (Fin ((X.Pj 0).m + 1) → (X.Pj 0).Qq (X.vJ 0 v))) :
    X.latAt v 0 (Function.update L' (X.vJ 0 v) L1) = L1 :=
  Function.update_self (β := fun u => Submodule ((X.Pj 0).W u) (Fin ((X.Pj 0).m + 1) → (X.Pj 0).Qq u))
    (X.vJ 0 v) L1 L'

theorem countG (hC : CountLoc) (v : X.Pl) (j i : ℕ) (L : (X.Pj j).Tup) (L' : (X.Pj (j + 1)).Tup)
    (hL : (X.Pj j).IsLatTup L) (hL' : (X.Pj (j + 1)).IsLatTup L') :
    ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
        X.ind v j L (Function.update L' (X.vJ (j + 1) v) L1) =
      ∑ l ∈ range (i + 1), nC X v i l •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) (L (X.vJ j v)), X.ind v j (Function.update L (X.vJ j v) A1) L' := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]
  cases j with
  | zero =>
    have key := count_fun hC p (X.G.P.n' v) (X.G.P.setting v).frac_alt (X.G.P.setting v).p_unif (X.G.P.setting v).res_card
      (X.G.P.m + 1) (X.G.P.m + (0 + 1) * (X.Fl.t + 1) + 1) (X.Fl.t + 1) i (by ring) (L v) (L' v) (hL v) (hL' v)
      (EE (X.Pj (0 + 1)) (X.vJ (0 + 1) v) i (L' v)) (fun B1 => mem_EE _)
      (fun k => UP (X.Pj (0)) (X.vJ (0) v) k (L v)) (fun k A1 => mem_UP _) x
    refine Eq.trans ?_ (key.trans ?_)
    · refine Finset.sum_congr rfl fun L1 _ => ?_
      unfold Sys.ind
      rw [latAt_succ_upd]
      rfl
    · symm
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [nsmul_eq_mul]
      refine congrArg₂ _ rfl (Finset.sum_congr rfl fun A1 _ => ?_)
      unfold Sys.ind
      rw [latAt_zero_upd]
      rfl
  | succ j =>
    have key := count_fun hC p (X.G.P.n' v) (X.G.P.setting v).frac_alt (X.G.P.setting v).p_unif (X.G.P.setting v).res_card
      (X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1) (X.G.P.m + ((j + 1) + 1) * (X.Fl.t + 1) + 1) (X.Fl.t + 1) i (by ring) (L v) (L' v) (hL v) (hL' v)
      (EE (X.Pj ((j + 1) + 1)) (X.vJ ((j + 1) + 1) v) i (L' v)) (fun B1 => mem_EE _)
      (fun k => UP (X.Pj ((j + 1))) (X.vJ ((j + 1)) v) k (L v)) (fun k A1 => mem_UP _) x
    refine Eq.trans ?_ (key.trans ?_)
    · refine Finset.sum_congr rfl fun L1 _ => ?_
      unfold Sys.ind
      rw [latAt_succ_upd]
      rfl
    · symm
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [nsmul_eq_mul]
      refine congrArg₂ _ rfl (Finset.sum_congr rfl fun A1 _ => ?_)
      unfold Sys.ind
      rw [latAt_succ_upd]
      rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
