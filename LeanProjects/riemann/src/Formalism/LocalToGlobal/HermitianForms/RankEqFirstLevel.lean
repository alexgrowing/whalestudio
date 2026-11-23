import Formalism.LocalToGlobal.HermitianColumns.StarConj
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.HermitianForms.DefsChi

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

def reGL {a b : ℕ} (h : a = b) (R : Type) [CommRing R] : GL (Fin a) R ≃* GL (Fin b) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (finCongr h)).toMulEquiv

def reV {a b : ℕ} (h : a = b) (E : Type) [Field E] : (Fin a → E) ≃ₗ[E] (Fin b → E) :=
  LinearEquiv.funCongrLeft E E (finCongr h).symm

def reL {a b : ℕ} (h : a = b) {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin a → E)) :
    Submodule (𝓞 E) (Fin b → E) :=
  L.map ((reV h E : (Fin a → E) →ₗ[E] (Fin b → E)).restrictScalars (𝓞 E))

structure SameCar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ} (h : a = b)
    {cls : Type} {stab : cls → Type}
    (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin a) (E ⊗[F] v.adicCompletion F)))
    (Uloc' : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin b) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (U' : Subgroup (GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (y : cls → GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (y' : cls → GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (st : ∀ c, stab c → GL (Fin a) E) (st' : ∀ c, stab c → GL (Fin b) E) : Prop where
  Lb_eq : Lb' = reL h Lb
  Uloc_eq : ∀ v, Uloc' v = (Uloc v).map (reGL h _).toMonoidHom
  U_eq : U' = U.map (reGL h _).toMonoidHom
  y_eq : ∀ c, y' c = reGL h _ (y c)
  st_eq : ∀ c s, st' c s = reGL h _ (st c s)

end Re

theorem rank_eq_first_level (R : Ranks) : R.k = R.N 0 := by
  simp [Ranks.N]

def crdN (D : D7) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : D7) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)

set_option maxHeartbeats 4000000 in

structure Joint {D : D7} (X : Formalism.L2.Herm.ColsHerm D) (u : D.what₂.Word) (T : FormsTied D u) : Prop where

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

  pr : ∀ (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Ld D u i c) (z' : Ld D u i hi c),
    z'.1 = crdN D i hi z.1 → (T.lv i hi).pr v c z' = (X.atT u).pr i v c z
  prk : ∀ (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Lk D u ((X.atT u).Pv v) i c) (z' : Lk T.atT i hi v c),
    z'.1 = crdN D i hi z.1 → (T.lv i hi).prk v c z' = (X.atT u).prk i v c z

  z0 : T.til.z0 = crdN D D.R.m le_rfl (X.atT u).z0
  ga : ∀ c, (T.til.ga c).1 = reGL (rankN D D.R.m le_rfl) _
    (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame ((X.atT u).tilG c).1)

  sp : T.gl.sp = (X.base.lev0 u).splitG
  piG : T.gl.piG = (X.levelZeroCompatibility u).piG
  fr0 : ∀ i v h, (T.glev 0 (Nat.zero_le _)).fr i v h = reGL (rank_eq_first_level D.R) _ ((X.base.lev0 u).frG i v h)

structure ColsTied (D : D7) where
  herm : Formalism.L2.Herm.ColsHerm D
  forms : ∀ u : D.what₂.Word, FormsTied D u
  joint : ∀ u, Joint herm u (forms u)
  gl_const : ∀ u u', (forms u).gl = (forms u').gl

  chi : CharacterCompatible (forms D.u₀).gl D.R.m

  fr_const : ∀ u u' (i : ℕ) (hi : i ≤ D.R.m), i < D.R.m → ((forms u).glev i hi).fr = ((forms u').glev i hi).fr
  frP_const : ∀ u u', (forms u).glevP.fr = (forms u').glevP.fr

structure ColsFull {D : D7} (C : ColsTied D) where
  full : Formalism.L2.Herm.FullTied D
  cols_eq : full.cols = C.herm

def ColumnsExtraCompatible {D : D7} {C : ColsTied D} (Fu : ColsFull C) {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    (ex : Extra D L hT Gi Gl K Y cX) : Prop :=
  Formalism.L2.Herm.ExtraTied Fu.full ex

theorem ColsTied.chi_all {D : D7} (C : ColsTied D) (u : D.what₂.Word) : CharacterCompatible (C.forms u).gl D.R.m := by
  rw [C.gl_const u D.u₀]
  exact C.chi

theorem FormsTied.chi_unit {D : D7} {u : D.what₂.Word} (T : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m)
    (x : (T.cls i hi).lev.U) : ‖(((T.cls i hi).lev.chi x : ℂˣ) : ℂ)‖ = 1 :=
  (T.glev i hi).chi_unit x

end Formalism.L2.Forms

end
