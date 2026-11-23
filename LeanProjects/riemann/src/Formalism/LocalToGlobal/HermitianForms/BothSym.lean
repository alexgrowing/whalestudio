import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
import Formalism.LocalToGlobal.HermitianColumns.SymAll

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def chM {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (u : D.what₂.Word) : H.Ch u D.R.m :=
  @default _ (H.Ch_m u).some.toInhabited

theorem chOf_m {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (u : D.what₂.Word) (c : (D.mem u).C.cls D.R.m) :
    H.chOf u D.R.m c = chM H u :=
  (H.Ch_m u).some.uniq _

theorem one_le_m (R : Ranks) : 1 ≤ R.m := by
  have h2 := R.two_le_m
  omega

set_option maxHeartbeats 4000000 in

structure ColsTiedSym (D : D7) where
  herm : Formalism.L2.Herm.ColsHermS D
  forms : ∀ u : D.what₂.Word, FormsTiedSym D u (herm.base.Ch u) (herm.base.chOf u)

  eV : ∀ u, (forms u).atT.eV = herm.base.vT u
  piU : ∀ u, (forms u).atT.piU = (herm.atT u).piU
  res : ∀ u, (forms u).atT.res = (herm.atT u).res

  car0 : ∀ u, SameCar (rank_eq_first_level D.R) (herm.base.lev0 u).Lb ((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
    (herm.base.lev0 u).Uloc ((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
    (herm.base.lev0 u).U ((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
    (fun c => ((herm.base.lev0 u).y c).1) (fun c => (((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
    (fun c s => ((herm.base.lev0 u).stabI c s).1) (fun c s => (((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1)

  carC : ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : herm.base.Ch u i),
    SameCar (rankN D i (le_of_succ_m h2)) (herm.base.lev u i h1 (le_of_succ_m h2) β).Lb ((forms u).ch i h1 h2 β).lev.Lb
      (herm.base.lev u i h1 (le_of_succ_m h2) β).Uloc ((forms u).ch i h1 h2 β).lev.Uloc
      (herm.base.lev u i h1 (le_of_succ_m h2) β).U ((forms u).ch i h1 h2 β).lev.U
      (fun c => ((herm.base.cls u i h1 (le_of_succ_m h2) β).y c).1) (fun c => (((forms u).ch i h1 h2 β).y c).1)
      (fun c s => ((herm.base.cls u i h1 (le_of_succ_m h2) β).stabI c s).1) (fun c s => (((forms u).ch i h1 h2 β).stabI c s).1)

  carM : ∀ u, SameCar (rankN D D.R.m le_rfl) (herm.base.lev u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).Lb
      ((forms u).cls D.R.m le_rfl (Or.inr rfl)).lev.Lb
      (herm.base.lev u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).Uloc ((forms u).cls D.R.m le_rfl (Or.inr rfl)).lev.Uloc
      (herm.base.lev u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).U ((forms u).cls D.R.m le_rfl (Or.inr rfl)).lev.U
      (fun c => ((herm.base.cls u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).y ⟨c, chOf_m herm.base u c⟩).1)
      (fun c => (((forms u).cls D.R.m le_rfl (Or.inr rfl)).y c).1)
      (fun c s => ((herm.base.cls u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).stabI ⟨c, chOf_m herm.base u c⟩ s).1)
      (fun c s => (((forms u).cls D.R.m le_rfl (Or.inr rfl)).stabI c s).1)

  carP : ∀ u, SameCar (rankP D) (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) (forms u).clsP.lev.Lb
    (herm.atT u).levP.Uloc (forms u).clsP.lev.Uloc (herm.atT u).levP.U (forms u).clsP.lev.U
    (fun c => ((herm.atT u).clsP.y c).1) (fun c => ((forms u).clsP.y c).1)
    (fun c s => ((herm.atT u).clsP.stabI c s).1) (fun c s => ((forms u).clsP.stabI c s).1)
  lattice₂ : ∀ u c, (forms u).clsP.lat c = ((herm.atT u).lattice₂ c).map
    ((crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E))

  pr : ∀ u (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Ld D u i c) (z' : Ld D u i hi c),
    z'.1 = crdN D i hi z.1 → ((forms u).lv i hi).pr v c z' = (herm.atT u).pr i v c z
  prk : ∀ u (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Lk D u ((herm.atT u).Pv v) i c) (z' : Lk (forms u).atT i hi v c),
    z'.1 = crdN D i hi z.1 → ((forms u).lv i hi).prk v c z' = (herm.atT u).prk i v c z
  prC : ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) v c (z : Formalism.L2.Herm.Ld D u i c)
    (z' : LdG D i (le_of_succ_m h2) (clsCrd D u i (le_of_succ_m h2) c)),
    z'.1 = crdN D i (le_of_succ_m h2) z.1 → ((forms u).lvC i h1 h2).pr v c z' = (herm.atT u).pr i v c z

  z0 : ∀ u, (forms u).til.z0 = crdN D D.R.m le_rfl (herm.atT u).z0
  ga : ∀ u c, ((forms u).til.ga c).1 = reGL (rankN D D.R.m le_rfl) _
    (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame ((herm.atT u).tilG c).1)

  sp : ∀ u, (forms u).gl.sp = (herm.base.lev0 u).splitG
  piG : ∀ u, (forms u).gl.piG = (herm.levelZeroCompatibility u).piG
  fr0 : ∀ u i v h, (forms u).glev0.fr i v h = reGL (rank_eq_first_level D.R) _ ((herm.base.lev0 u).frG i v h)
  gl_const : ∀ u u', (forms u).gl = (forms u').gl

  chi : CharacterCompatible (forms D.u₀).gl D.R.m

  frame_level_zero_const : ∀ u u', (forms u).glev0.fr = (forms u').glev0.fr
  frP_const : ∀ u u', (forms u).glevP.fr = (forms u').glevP.fr

set_option maxHeartbeats 4000000 in

structure OneLevelSymmetricColumns (D : D7) extends ColsTiedSym D where
  Ch_one : ∀ u i, Subsingleton (herm.base.Ch u i)
  H_eq : ∀ u i (_ : 1 ≤ i) (_ : i + 2 ≤ D.R.m) β a v hv, (forms u).H i β a v hv = HXS D i v
  lamC_eq : ∀ u i (_ : 1 ≤ i) (_ : i + 2 ≤ D.R.m) β a v hv (M : (forms u).H i β a v hv),
    (((forms u).lamC i β a v hv M : ℂˣ) : ℂ) =
      lamX ((forms u).gl.psi0 a v hv) ((forms u).gl.chiB a v hv) (D.R.N i) D.R.k (rSD D.R) D.R.t (D.R.m - 1 - i) i (k_le_N D.R i)
        ((M : GL (Fin (D.R.N i)) (kv D.host.F v)) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (kv D.host.F v))
  Yb_one : ∀ u, Subsingleton (forms u).Yb

end Formalism.L2.Forms

end
