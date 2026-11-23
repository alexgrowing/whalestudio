import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumns

noncomputable section

namespace GlobalTheory.TwU.AtTrue.Cl

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ)
  (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E)

def TChain : Prop :=
  IsChainTopW t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) (t.rd u μ) t.seam.σ₀ (t.word u) t.m2
    (fun i hi => A.pt i (hi.trans (cpl_lt t μ).le))
    (fun i hi c => A.ib i ((Nat.lt_succ_of_le hi).trans (cpl_lt t μ)) ((St i _).chOf c)) A.yb (A.pt _ (top_le t μ))

def TTeq : Prop := ∀ i hi, (St i hi).T = (D.mem u).A.T

def TBad : Prop := ∀ i hi, ∀ v ∈ (St i hi).bad, UnderSB t μ v

def TLat : Prop := ∀ i hi c, t.seam.lat ((t.rd u μ).N i c) =
    latCo D.sp (gramN D i hi) (A.crd i hi) a ((St i hi).y c).1 ((St i hi).K ((St i hi).chOf c)).lev.Lb

def TFrame : Prop := ∀ i hi c (P : SB t μ), NearAt (seamP t.seam P.1) ((t.cst μ).D P)
    (A.mov i hi c * ratA D.host.F (A.fb i hi ((St i hi).chOf c) P)) (seamGL t.seam (frsF t.sel (t.tup μ) (A.pt i hi c) P))

def TFnl : Prop := ∀ i hi (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
    IsOver v (seamP t.seam P.1) → ∃ ι : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal,
      ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1

def TCoset : Prop := ∀ c, ∀ y ∈ A.yb c, ∀ P : SB t μ, SameCoset t.sel (t.tup μ) (t.cst μ) P
    ((frsF t.sel (t.tup μ) (A.pt _ (cpl_lt t μ).le c) P).symm y) (A.y0 ((St _ (cpl_lt t μ).le).chOf c) P)

def TLevMid : Prop := ∀ i (hi : i < D.R.m), i ≤ t.m2 → ∀ β,
    LocLe t.seam ((St i hi.le).K β).lev (A.fb i hi.le β) (t.cst μ).D (A.midRel i hi β) ∧
    LocGe t.seam ((St i hi.le).K β).lev (A.fb i hi.le β) (t.cst μ).D (A.midRel i hi β) ∧
    ChiIs t.seam ((St i hi.le).K β).lev (A.fb i hi.le β) (t.cst μ).D (A.midRel i hi β)

def TLevCpl : Prop := ∀ β,
    LocLe t.seam ((St _ (cpl_lt t μ).le).K β).lev (A.fb _ _ β) (t.cst μ).D (A.cplRel β) ∧
    LocGe t.seam ((St _ (cpl_lt t μ).le).K β).lev (A.fb _ _ β) (t.cst μ).D (A.cplRel β) ∧
    ChiIs t.seam ((St _ (cpl_lt t μ).le).K β).lev (A.fb _ _ β) (t.cst μ).D (A.cplRel β)

def TLevTop : Prop := ∀ β,
    LocLe t.seam ((St _ (top_le t μ)).K β).lev (A.fb _ _ β) (topDep t.sel (t.tup μ) (t.cst μ))
      (TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1)) ∧
    ChiIs t.seam ((St _ (top_le t μ)).K β).lev (A.fb _ _ β) (topDep t.sel (t.tup μ) (t.cst μ))
      (TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1))

def TDt : Prop := ∀ i hi c (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det ((St i hi).y c).1 → (t.O u μ).dt i c = dtU y

def TAa : Prop := t.amb.AAUnit (Sall t.sel (t.tup μ) (t.word u))

variable {t u μ St A dtU a}

end Gen

section Std

open GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC}
  {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
  (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi)
  (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (K : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi))

structure IsStd (A : AdData t u a (charts I l Z u a bad Ch chOf eY K)) : Prop where
  crd : ∀ i hi, A.crd i hi = 1
  iA : HEq A.iA (RingEquiv.refl (AfE B.host.F B.host.E))
  q : HEq A.q ((QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)))
  pt : HEq A.pt (fun i (_ : i ≤ B.R.m) (c : (I.stp u a i).Cl) => ((I.stp u a i).rep c).1.1)
  yb : HEq A.yb (fun c : (I.stp u a (B.R.m - 2 + 1)).Cl => ((I.stp u a (B.R.m - 2 + 1)).rep c).1.2)
  ib : ∀ i (hi : i < B.R.m) (c : (I.stp u a i).Cl), HEq (A.ib i hi (chOf i hi.le c)) (Idx.get c.1 hi)
  fb : ∀ i hi β P, A.fb i hi β P = 1
  y0 : ∀ (h : B.R.m - 2 + 1 ≤ B.R.m) (c : (I.stp u a (B.R.m - 2 + 1)).Cl) (P : rowSG (B.primes X) I.sel (I.tup a))
    (β : (charts I l Z u a bad Ch chOf eY K (t.m2 + 1) (cpl_lt t a).le).Ch) (P' : SB t a),
    HEq β (chOf (B.R.m - 2 + 1) h c) → HEq P' P → (cosetIn ((I.stp u a (B.R.m - 2 + 1)).rep c) P).Nonempty →
      ∃ y ∈ cosetIn ((I.stp u a (B.R.m - 2 + 1)).rep c) P, HEq (A.y0 β P') y

def Hyp (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) (A : AdData t u a (charts I l Z u a bad Ch chOf eY K)) : Prop :=
  I.Ok ∧ TC.Pins B X ∧ StdData I l Z t dt ∧ Side I l Z u a bad Ch chOf eY K ∧ (∀ i hi, ReadsOne I l Z u a i hi (chOf i hi) (K i hi)) ∧
    IsStd I l Z t u a bad Ch chOf eY K A

end Std

section Pf

open GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

end Pf

end GlobalTheory.TwU.AtTrue.Cl

end
