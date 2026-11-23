import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulUpdate

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime]

theorem Tm_add (X : Sys p) (v : X.Pl) (i J : ℕ) (F F' : X.Fm J) :
    X.Tm v i J (F + F') = X.Tm v i J F + X.Tm v i J F' := by
  funext c L
  show (X.Pj J).Tminus (X.vJ J v) i (F c + F' c) L =
    (X.Pj J).Tminus (X.vJ J v) i (F c) L + (X.Pj J).Tminus (X.vJ J v) i (F' c) L
  rw [tm_eq, tm_eq, tm_eq, ← Finset.sum_add_distrib]
  rfl

theorem Tm_smul (X : Sys p) (v : X.Pl) (i J : ℕ) (a : X.G.Kf) (F : X.Fm J) :
    X.Tm v i J (a • F) = a • X.Tm v i J F := by
  funext c L
  show (X.Pj J).Tminus (X.vJ J v) i (a • F c) L = a • (X.Pj J).Tminus (X.vJ J v) i (F c) L
  rw [tm_eq, tm_eq, Finset.smul_sum]
  rfl

theorem Tt_add (X : Sys p) (v : X.Pl) (i J : ℕ) (F F' : X.Fm J) :
    X.Tt v i J (F + F') = X.Tt v i J F + X.Tt v i J F' := by
  unfold Sys.Tt
  split_ifs
  · rfl
  · rw [Tm_add, smul_add]

theorem Tt_smul (X : Sys p) (v : X.Pl) (i J : ℕ) (a : X.G.Kf) (F : X.Fm J) :
    X.Tt v i J (a • F) = a • X.Tt v i J F := by
  unfold Sys.Tt
  split_ifs
  · rfl
  · rw [Tm_smul, smul_comm]

def TtLinF (X : Sys p) (v : X.Pl) (i J : ℕ) : X.Fm J →ₗ[X.G.Kf] X.Fm J where
  toFun := X.Tt v i J
  map_add' := Tt_add X v i J
  map_smul' := Tt_smul X v i J

@[simp] theorem TtLinF_apply (X : Sys p) (v : X.Pl) (i J : ℕ) (F : X.Fm J) : TtLinF X v i J F = X.Tt v i J F := rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
