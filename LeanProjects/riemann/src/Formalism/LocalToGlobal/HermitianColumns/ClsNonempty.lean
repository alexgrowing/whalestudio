import Formalism.LocalToGlobal.HermitianColumns.CoordinateLatticeSelfDual
import Formalism.LocalToGlobal.HermitianColumns.CocycleZeroMemInvariants

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Ad0 (D : D7) (H : HermCols D) (u : D.what₂.Word) (c c' : (D.mem u).C.cls 0) (γ : GX D 0)
    (v : (D.mem u).A.vT) : Prop :=
  AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y c')
    (toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) γ.1) (H.vT u v).1

def AdI (D : D7) (H : HermCols D) (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m)
    (c c' : (D.mem u).C.cls i) (γ : GX D i) (v : (D.mem u).A.vT) : Prop :=
  AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c) ((H.cls u i h1 hm).y c')
    (toGLb (D.sp.X i).frame γ.1) (H.vT u v).1

structure AdTied (D : D7) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop where
  up0 : ∀ u v c (y : Ld D u 0 c), (D.fm u).fv 0 v c ((aT u).pr 0 v c y) = 1 →
    Ad0 D H u c ((D.fm u).up 0 v c ((aT u).pr 0 v c y)) ((aT u).upG 0 v c y) v
  upI : ∀ u i h1 hm v c (y : Ld D u i c), (D.fm u).fv i v c ((aT u).pr i v c y) = 1 →
    AdI D H u i h1 hm c ((D.fm u).up i v c ((aT u).pr i v c y)) ((aT u).upG i v c y) v
  dn0 : ∀ u v c g, g ≠ 0 → Ad0 D H u c ((D.fm u).dn 0 v c g) ((aT u).dnG 0 v c g) v
  dnI : ∀ u i h1 hm v c g, g ≠ 0 → AdI D H u i h1 hm c ((D.fm u).dn i v c g) ((aT u).dnG i v c g) v
  dil0 : ∀ u v a c, Ad0 D H u c ((D.fm u).dil 0 v a c) ((aT u).dilG 0 v a c) v
  dilI : ∀ u i h1 hm v a c, AdI D H u i h1 hm c ((D.fm u).dil i v a c) ((aT u).dilG i v a c) v

theorem HermTied.cls_nonempty {D : D7} (H : HermTied D) (u : D.what₂.Word) (i : ℕ) (hm : i ≤ D.R.m) :
    Nonempty ((D.mem u).C.cls i) := by
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · obtain ⟨c, _⟩ := (H.lev0 u).y_bij.2 (Quotient.mk'' 1)
    exact ⟨c⟩
  · exact (H.cls u i h1 hm).nonempty

end Formalism.L2.Herm

end
