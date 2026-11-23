import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.LocalToGlobal.HermitianForms.BothSym

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormsTiedSym.to0 {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : FormsTiedSym D u Ch chOf) : Forms0 D u where
  atT := T.atT
  cls0 := T.cls 0 (Nat.zero_le _) (Or.inl rfl)
  val0 := T.val 0 (Nat.zero_le _) (Or.inl rfl)
  gl := T.gl
  gl_K := T.gl_K
  glev0 := T.glev0
  lv0 := T.lv 0 (Nat.zero_le _)
  fMe0 := T.fMe 0 (Nat.zero_le _) (Or.inl rfl)
  fv0 := T.fv 0 (Nat.zero_le _) (Or.inl rfl)
  up_natural_level_zero := T.upN 0 (Nat.zero_le _) (Or.inl rfl)
  down_natural_level_zero := T.dnN 0 (Nat.zero_le _) (Or.inl rfl)
  norm0 := T.norm 0 (Nat.zero_le _) (Or.inl rfl)
  bw0 := T.bw 0 (Nat.zero_le _) (Or.inl rfl)

theorem ColsTiedSym.joint0 {D : D7} (C : ColsTiedSym D) (u : D.what₂.Word) :
    Joint0 C.herm.base.lev0 u (C.forms u).to0 := C.car0 u

end Formalism.L2.Forms
