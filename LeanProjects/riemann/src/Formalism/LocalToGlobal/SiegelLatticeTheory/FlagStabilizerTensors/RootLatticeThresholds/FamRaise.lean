import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

noncomputable section

namespace Formalism.MainNotions

theorem raise_lt {eps : ℝ} {Fm : FamP eps} {y x : ℝ} (h : max Fm.x1 y < x) : Fm.x1 < x :=
  lt_of_le_of_lt (le_max_left _ _) h

def FamP.raise {eps : ℝ} (Fm : FamP eps) (y : ℝ) : FamP eps :=
  { Fm with
    x1 := max Fm.x1 y
    one_lt_family_threshold := lt_of_lt_of_le Fm.one_lt_family_threshold (le_max_left _ _)
    L_x := fun x i h => Fm.L_x x i (raise_lt h)
    o_le_Co := fun x i h => Fm.o_le_Co x i (raise_lt h)
    QS_le_Co := fun x i h => Fm.QS_le_Co x i (raise_lt h)
    bTop_eq := fun x h => Fm.bTop_eq x (raise_lt h)
    bTop_ge := fun x h => Fm.bTop_ge x (raise_lt h)
    bT_le := fun x h => Fm.bT_le x (raise_lt h)
    coverS := fun x h => Fm.coverS x (raise_lt h)
    params := fun x h => Fm.params x (raise_lt h)
    params_K := fun x h => Fm.params_K x (raise_lt h)
    parT := fun x h => Fm.parT x (raise_lt h)
    parT_K := fun x h => Fm.parT_K x (raise_lt h)
    sizes := fun x h => Fm.sizes x (raise_lt h)
    supp_sat := fun x h => Fm.supp_sat x (raise_lt h)
    tw_supp := fun x h => Fm.tw_supp x (raise_lt h)
    fills := fun x h => Fm.fills x (raise_lt h)
    lats0 := fun x h => Fm.lats0 x (raise_lt h)
    latTied := fun x h => Fm.latTied x (raise_lt h)
    nuDef := fun x h => Fm.nuDef x (raise_lt h)
    nprimeDef := fun x h => Fm.nprimeDef x (raise_lt h)
    rrDef := fun x h => Fm.rrDef x (raise_lt h)
    h_eq := fun x h => Fm.h_eq x (raise_lt h)
    ex := fun x h => Fm.ex x (raise_lt h)
    rho_le := fun x h => Fm.rho_le x (raise_lt h)
    drop_iff := fun x h => Fm.drop_iff x (raise_lt h)
    fixed := ⟨Fm.fixed.1, Fm.fixed.2.1, Fm.fixed.2.2.1, Fm.fixed.2.2.2.1, Fm.fixed.2.2.2.2.1, Fm.fixed.2.2.2.2.2.1,
      Fm.fixed.2.2.2.2.2.2.1, fun x h => Fm.fixed.2.2.2.2.2.2.2 x (raise_lt h)⟩ }

@[simp] theorem raise_lower_endpoint {eps : ℝ} (Fm : FamP eps) (y : ℝ) : (Fm.raise y).x1 = max Fm.x1 y := rfl

theorem ownEv_raise {eps : ℝ} (Fm : FamP eps) (y : ℝ) {P : ℝ → ℝ → ∀ x, Fm.Ix x → Prop} :
    Formalism.MainNotions.S.OwnEv (Fm.raise y) P ↔ Formalism.MainNotions.S.OwnEv Fm P := Iff.rfl

end Formalism.MainNotions
