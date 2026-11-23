import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.Forms

open Formalism.BasicNotions

theorem Forms0.up {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0) :
    UpTie (T.lv i hi h) (T.cls i hi h) (T.val i hi h) := by
  subst h
  show UpTie T.lv0 T.cls0 T.val0
  exact UpNatTie.upTie T.up_natural_level_zero

theorem Forms0.dn {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0) :
    DnTie (T.lv i hi h) (T.cls i hi h) (T.val i hi h) := by
  subst h
  show DnTie T.lv0 T.cls0 T.val0
  exact DnNatTie.dnTie T.down_natural_level_zero

theorem Forms0.chi_unit {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0)
    (x : (T.cls i hi h).lev.U) : ‖((T.cls i hi h).lev.chi x : ℂ)‖ = 1 := by
  subst h
  exact T.glev0.chi_unit x

end Formalism.L2.Forms

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms

def ChiFin0 {D : D7} {u : D.what₂.Word} (T : Forms0 D u) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ i (hi : i ≤ D.R.m) (h0 : i = 0) (x : (T.cls i hi h0).lev.U),
    (((T.cls i hi h0).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((T.cls i hi h0).lev.chi x : ℂˣ) : ℂ)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
