import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianColumns.TiedCh

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SymmetricLevelZeroData (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ u, ColLevelX (H.lev0 u) (fun x => x ∈ D.host.K) (aT u).piU (H.vT u)
    (fun v c z => (D.fm u).fv 0 v c ((aT u).pr 0 v c z))

def Ad0S (D : D7) (H : HermColsCh D) (u : D.what₂.Word) (c c' : (D.mem u).C.cls 0) (γ : GX D 0)
    (v : (D.mem u).A.vT) : Prop :=
  AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y c')
    (toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) γ.1) (H.vT u v).1

def AdIS (D : D7) (H : HermColsCh D) (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m)
    (c c' : (D.mem u).C.cls i) (γ : GX D i) (v : (D.mem u).A.vT) : Prop :=
  ∃ h : H.chOf u i c' = H.chOf u i c,
    AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm (H.chOf u i c)).U
      ((H.cls u i h1 hm (H.chOf u i c)).y ⟨c, rfl⟩) ((H.cls u i h1 hm (H.chOf u i c)).y ⟨c', h⟩)
      (toGLb (D.sp.X i).frame γ.1) (H.vT u v).1

structure SymmetricAdelicCompatibility (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop where
  up0 : ∀ u v c (y : Ld D u 0 c), (D.fm u).fv 0 v c ((aT u).pr 0 v c y) = 1 →
    Ad0S D H u c ((D.fm u).up 0 v c ((aT u).pr 0 v c y)) ((aT u).upG 0 v c y) v
  upI : ∀ u i h1 hm v c (y : Ld D u i c), (D.fm u).fv i v c ((aT u).pr i v c y) = 1 →
    AdIS D H u i h1 hm c ((D.fm u).up i v c ((aT u).pr i v c y)) ((aT u).upG i v c y) v
  dn0 : ∀ u v c g, g ≠ 0 → Ad0S D H u c ((D.fm u).dn 0 v c g) ((aT u).dnG 0 v c g) v
  dnI : ∀ u i h1 hm v c g, g ≠ 0 → AdIS D H u i h1 hm c ((D.fm u).dn i v c g) ((aT u).dnG i v c g) v
  dil0 : ∀ u v a c, Ad0S D H u c ((D.fm u).dil 0 v a c) ((aT u).dilG 0 v a c) v
  dilI : ∀ u i h1 hm v a c, AdIS D H u i h1 hm c ((D.fm u).dil i v a c) ((aT u).dilG i v a c) v

def SymmetricCofactorCompatibility (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ u, D.cOf u * ((aT u).piU : D.host.E) = ((aT D.u₀).piU : D.host.E)

def PiGConstS (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (X : SymmetricLevelZeroData D H aT) : Prop :=
  ∀ u u', (X u).piG = (X u').piG

def stabPLinS (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (u : D.what₂.Word)
    (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c) : D.sp.X'.V ≃ₗ[D.host.E] D.sp.X'.V :=
  (toGLb D.sp.X'.frame).symm ((aT u).clsP.stabI c s : GL (Fin D.sp.X'.rank) D.host.E)

def stabMLinS (D : D7) (H : HermColsCh D) (u : D.what₂.Word) (h1 : 1 ≤ D.R.m)
    (c : (D.mem u).C.cls D.R.m) (s : (D.mem u).C.stab D.R.m c) :
    (D.sp.X D.R.m).V ≃ₗ[D.host.E] (D.sp.X D.R.m).V :=
  (toGLb (D.sp.X D.R.m).frame).symm
    ((H.cls u D.R.m h1 le_rfl (H.chOf u D.R.m c)).stabI ⟨c, rfl⟩ s : GL (Fin (D.sp.X D.R.m).rank) D.host.E)

def SymmetricStabilizerMapCompatibility (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (h1 : 1 ≤ D.R.m) (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c),
    (∀ x : D.sp.X'.V,
      ((aT u).tilG c).1 (stabMLinS D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (D.sp.iX' x))) =
        D.sp.iX' (stabPLinS D H aT u c s x)) ∧
    ((aT u).tilG c).1 (stabMLinS D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (aT u).z0)) = (aT u).z0

def SymmetricResidueFieldLevels (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u i),
    FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 hm β).Lb (H.cls u i h1 hm β).y (fun c => D.clsLat u i c.1) (H.vT u v).1
      ((D.mem u).A.Fv v) (fun c z => (D.fm u).fv i v c.1 ((aT u).pr i v c.1 z))

def SymmetricBaseCompatibility (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj ((aT u).piU : D.host.E) →
    ((H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 D.host.E)
        (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0) ∧
    ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : H.Ch u i),
      (H.lev u i h1 hm β).Lb ⊔ Ideal.span {pb} • dualL D.sp.cm (D.sp.X i) (H.lev u i h1 hm β).Lb =
        crdLat (D.sp.X i) (D.sp.X i).L0

structure ColsHermS (D : D7) where
  base : HermColsCh D
  atT : ∀ u, AtT D u (base.vT u) (base.Fv u)
  levelZeroCompatibility : SymmetricLevelZeroData D base atT
  ad : SymmetricAdelicCompatibility D base atT
  cof : SymmetricCofactorCompatibility D base atT
  piG : PiGConstS D base atT levelZeroCompatibility
  stabMap : SymmetricStabilizerMapCompatibility D base atT
  fvI : SymmetricResidueFieldLevels D base atT
  std : StdTied D
  baseL : SymmetricBaseCompatibility D base atT

end Formalism.L2.Herm

end
