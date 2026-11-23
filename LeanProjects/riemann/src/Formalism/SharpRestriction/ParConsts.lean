import Formalism.SharpRestriction.FamCore
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.DataParamsT
import Formalism.LocalRingCardinality.KernelPlaceMeanBound
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataGatTies
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

def parConsts {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : List ℝ :=
  [P.CkLow, P.Ck6, P.CfL, P.cLL, P.CnW, P.Crho, P.CDelG, P.CLw,
    P.Cj0, P.Cw, P.cw, P.CDel, P.CCount, P.Ch0r, P.Ch0k, P.Ch0N,
    P.Cgap, P.CetaF, P.CY, P.CYL, P.Cpde, P.CccK, P.CF]

def NoGain {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (Cr : ℝ) (p : ℕ) : Prop :=
  ((p : ℝ) < L.sc.X' * (1 + Cr * G.rhoB D K L.sc) ∧ G.IsResidueClassZero D p ∧
    ((addOrderOf (G.hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4) ∨
      (L.sc.p0 D.R.k ≤ (p : ℝ) ∧ ∃ i : ℕ, 1 ≤ i ∧ |(p : ℝ) ^ i - L.sc.X'| ≤ G.rhoB D K L.sc * L.sc.X') ∨
      (G.Cand D L K p ∧ L.sc.x ^ (-L.sc.eps) < G.Sig X K (G.aL L) (G.bL L) p))) ∨
  L.sc.X'' D.R.n < (p : ℝ) ∨ ¬ (G.IsResidueClassZero D p ∨ G.IsSg D p) ∨ G.IsCs D p

structure FamP (eps : ℝ) extends FamCore eps where

  params : ∀ x, x1 < x → ∀ i : Ix x, ParameterChoice' (D x i) (L x i)
  PK : List ℝ
  params_K : ∀ x (hx : x1 < x) i, parConsts (params x hx i) = PK

  parT : ∀ x (hx : x1 < x) (i : Ix x), ParamsT (D x i) (L x i) (params x hx i)
  PT : List ℝ
  parT_K : ∀ x (hx : x1 < x) i, [(parT x hx i).CP, (parT x hx i).eP, (parT x hx i).Cp, (parT x hx i).Cb,
    (parT x hx i).cTO, (parT x hx i).ChT, (parT x hx i).CbN] = PT

  CTu : ℝ

  sizes : ∀ x, x1 < x → ∀ i : Ix x, SizesAt (L x i)

  ties : ∀ x (i : Ix x), Ties (D x i)

  gatT : ∀ x (i : Ix x), GatTies (D x i)

  X : ∀ x (i : Ix x), DivX (D x i)

  Gx : ∀ x (i : Ix x), G.Inst (D x i) (L x i)
  Gy : ∀ x (i : Ix x), G.LatInst (D x i)
  GK : G.Consts
  GK_nonneg : GK.Nonneg

  supp_sat : ∀ x, x1 < x → ∀ (i : Ix x) w,
    (((D x i).what₂.places.resChar w : ℕ) : ℝ) ≤ (L x i).sc.X'' (D x i).R.n → w ∈ (L x i).supp

  tw_supp : ∀ x, x1 < x → ∀ (i : Ix x) w, (D x i).what₂.muAt w ≠ (D x i).what₂.mu0 → w ∈ (L x i).supp

  fills : ∀ x, x1 < x → ∀ (i : Ix x) w, G.ParametersFill (Gx x i) GK w
  lats0 : ∀ x, x1 < x → ∀ (i : Ix x) w u,
    G.VV (Gx x i) GK (G.aL (L x i)) (G.bL (L x i)) ((D x i).what₂.places.resChar w) = ∅ →
    (D x i).what₂.places.resChar w ≠ ((D x i).mem u).A.T → (L x i).lenMN u w = 0

  latTied : ∀ x, x1 < x → ∀ i : Ix x, G.LatTied (gatT x i) (Gx x i) (Gy x i)

  Csz : ℝ
  nuDef : ∀ x, x1 < x → ∀ i : Ix x, DV.NuDef (D x i) (L x i)
  nprimeDef : ∀ x, x1 < x → ∀ i : Ix x, DV.NprimeDef (D x i) (L x i)
  rrDef : ∀ x, x1 < x → ∀ i : Ix x, DV.RRDef (D x i)
  h_eq : ∀ x, x1 < x → ∀ (i : Ix x) u, (D x i).div.h u = DV.hExpl6 (D x i) (L x i) (X x i) Csz u

  cX : ExtraC

  ex : ∀ x, x1 < x → ∀ i : Ix x, Extra (D x i) (L x i) (gatT x i) (Gx x i) (Gy x i) GK (X x i) cX

  rho_le : ∀ x, x1 < x → ∀ i : Ix x, G.rhoB (D x i) GK (L x i).sc ≤ x ^ (-2 : ℝ)

  Cr : ℝ
  one_le_Cr : 1 ≤ Cr
  drop_iff : ∀ x, x1 < x → ∀ (i : Ix x) p, p.Prime →
    (p ∈ (L x i).drop ↔ NoGain (Gx x i) GK Cr p ∧ ∀ u, p ≠ ((D x i).mem u).A.T)

  fixed : GK.Pr1 = 1 ∧ GK.dl1 = 5 ∧ GK.dl2 = 4 ∧ cX.Ce = 1 ∧ cX.err.c6 = 12 ∧ cX.err.dig = 3 ∧ Cr = 1 ∧
    ∀ x (hx : x1 < x) (i : Ix x), (params x hx i).CnW = 10 ∧ 12 ≤ (parT x hx i).eP

  eta_eq : ∀ x (i i' : Ix x), (L x i).etaSz = (L x i').etaSz
  Sc_shared : ∀ x (i i' : Ix x), (L x i).Sc = (L x i').Sc
  hP_eq : ∀ x (i i' : Ix x) p, (G.hP (D x i) p).val = (G.hP (D x i') p).val
  bs_eq : ∀ x (i i' : Ix x) (h t : G.HH (D x i)) (h' t' : G.HH (D x i')), h.val = h'.val → t.val = t'.val →
    ((Gx x i).bs h t).val = ((Gx x i').bs h' t').val
  off_eq : ∀ x (i i' : Ix x) j (t : G.HH (D x i)) (t' : G.HH (D x i')), t.val = t'.val →
    (Gx x i).off j (false, t) = (Gx x i').off j (false, t')
  kapI_eq : ∀ x (i i' : Ix x), (Gx x i).kapI = (Gx x i').kapI
  ep_eq : ∀ x (i i' : Ix x), (Gx x i).ep = (Gx x i').ep

def DFamP : Type 1 := ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → FamP ε

end Formalism.MainNotions

end
