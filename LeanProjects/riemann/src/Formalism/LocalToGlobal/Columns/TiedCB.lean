import Formalism.LocalToGlobal.Columns.TiedCH
import Formalism.LocalToGlobal.Columns.TiedCG
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def crdN (D : ColRec) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : ColRec) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)

set_option maxHeartbeats 4000000 in

structure Joint {D : ColRec} (X : CH.ColsHerm D) (u : D.what₂.Word) (T : FormsTied D u) : Prop where

  eV : T.atT.eV = X.base.vT u
  piU : T.atT.piU = (X.atT u).piU
  res : T.atT.res = (X.atT u).res

  car0 : SameCar (rank_eq_first_level D.R) (X.base.lev0 u).Lb (T.cls 0 (Nat.zero_le _)).lev.Lb
    (X.base.lev0 u).Uloc (T.cls 0 (Nat.zero_le _)).lev.Uloc (X.base.lev0 u).U (T.cls 0 (Nat.zero_le _)).lev.U
    (fun c => ((X.base.lev0 u).y c).1) (fun c => ((T.cls 0 (Nat.zero_le _)).y c).1)
    (fun c s => ((X.base.lev0 u).stabI c s).1) (fun c s => ((T.cls 0 (Nat.zero_le _)).stabI c s).1)

  carI : ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m), SameCar (rankN D i hm) (X.base.lev u i h1 hm).Lb (T.cls i hm).lev.Lb
    (X.base.lev u i h1 hm).Uloc (T.cls i hm).lev.Uloc (X.base.lev u i h1 hm).U (T.cls i hm).lev.U
    (fun c => ((X.base.cls u i h1 hm).y c).1) (fun c => ((T.cls i hm).y c).1)
    (fun c s => ((X.base.cls u i h1 hm).stabI c s).1) (fun c s => ((T.cls i hm).stabI c s).1)

  carP : SameCar (rankP D) (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) T.clsP.lev.Lb
    (X.atT u).levP.Uloc T.clsP.lev.Uloc (X.atT u).levP.U T.clsP.lev.U
    (fun c => ((X.atT u).clsP.y c).1) (fun c => (T.clsP.y c).1)
    (fun c s => ((X.atT u).clsP.stabI c s).1) (fun c s => (T.clsP.stabI c s).1)
  lattice₂ : ∀ c, T.clsP.lat c = ((X.atT u).lattice₂ c).map
    ((crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E))

  pr : ∀ (i : ℕ) (hi : i ≤ D.R.m) v c (z : CH.Ld D u i c) (z' : Ld D u i hi c),
    z'.1 = crdN D i hi z.1 → (T.lv i hi).pr v c z' = (X.atT u).pr i v c z
  prk : ∀ (i : ℕ) (hi : i ≤ D.R.m) v c (z : CH.Lk D u ((X.atT u).Pv v) i c) (z' : Lk T.atT i hi v c),
    z'.1 = crdN D i hi z.1 → (T.lv i hi).prk v c z' = (X.atT u).prk i v c z

  z0 : T.til.z0 = crdN D D.R.m le_rfl (X.atT u).z0
  ga : ∀ c, (T.til.ga c).1 = reGL (rankN D D.R.m le_rfl) _
    (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame ((X.atT u).tilG c).1)

  sp : T.gl.sp = (X.base.lev0 u).splitG
  piG : T.gl.piG = (X.levelZeroCompatibility u).piG
  fr0 : ∀ i v h, (T.glev 0 (Nat.zero_le _)).fr i v h = reGL (rank_eq_first_level D.R) _ ((X.base.lev0 u).frG i v h)

structure ColsTied (D : ColRec) where
  herm : CH.ColsHerm D
  forms : ∀ u : D.what₂.Word, FormsTied D u
  joint : ∀ u, Joint herm u (forms u)
  gl_const : ∀ u u', (forms u).gl = (forms u').gl

  chi : CharacterCompatible (forms D.u₀).gl D.R.m

  fr_const : ∀ u u' (i : ℕ) (hi : i ≤ D.R.m), i < D.R.m → ((forms u).glev i hi).fr = ((forms u').glev i hi).fr
  frP_const : ∀ u u', (forms u).glevP.fr = (forms u').glevP.fr

end Formalism.L2.Col.CF

end
