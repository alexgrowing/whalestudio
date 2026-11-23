import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}

abbrev Val (B : GlobalTheory.Mem.Base) : Type := VV B.fields.K B.wts.sgTrue

abbrev Frm (I : TC B X) (a : I.ι) : Type := (mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a)).EqFun

def val {I : TC B X} {a : I.ι} (φ : Frm I a) (d : RowPt (B.primes X) B.R I.sel (I.tup a)) : Val B := φ.1 d

def IsRes {I : TC B X} {a : I.ι} (φ : Frm I a) {V : Type} (x : V) : Prop :=
  ∃ ok : (mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a)).Ok,
    HEq ((mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a)).res ok φ) x

def HasVal {I : TC B X} (l : I.Laws) (u : B.Word) {a : I.ι} (φ : Frm I a) (G : (I.per l u a).Mt) : Prop :=
  ∀ p : (I.stX a).D (), (show (I.perIn u a).Mt B.fields.emb B.embLL from G).1 () p =
    MvPolynomial.map B.embLL (val φ (toRow I.sel (I.tup a) p.1.1)).1

def latOf (I : TC B X) (a : I.ι) (y : TC.GA B (B.R.N B.R.m - 1)) : RowPt (B.primes X) B.R I.sel (I.tup a) :=
  letI := GlobalTheory.Mem.Col2.starE B
  decoOf (F := B.fields.F) (E := B.fields.E) ∅ (rowSG (B.primes X) I.sel (I.tup a)) y

def IsUni (B : GlobalTheory.Mem.Base) (y : TC.GA B (B.R.N B.R.m - 1)) : Prop := y ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N B.R.m - 1)

def pairVal (B : GlobalTheory.Mem.Base) (z : (GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1)) → ℂ) (w : Val B) : ℂ :=
  pairB B.wts.sgTrue (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf B.wts.sgTrue)
    (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) z) (MvPolynomial.map B.embLL w.1)

variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

def RecVal (u : B.Word) (a : (I.rec7 l Z).what₂.Tup) (φ : Frm I a) (G : (I.rec7 l Z).what₂.Amb a) : Prop :=
  (∀ h : a = (I.rec7 l Z).what₂.mu0, HasVal (a := I.mu0) l u (Eq.rec (motive := fun (ν : (I.rec7 l Z).what₂.Tup) _ => Frm I ν) φ h)
    (((I.rec7 l Z).eMt u).symm (Eq.rec (motive := fun ν _ => (I.rec7 l Z).what₂.Amb ν) G h))) ∧
  HasVal l u φ (((I.rec7 l Z).eMtTw u a).symm G)

variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)

def ValEqv (c : Val B →ₛₗ[B.embLL] (pk W).cX.W) : Prop :=
  ∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
    GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = (pk W).cX.ρ γ.1 (c v)

def pkAt (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') : (pk W).cX.W :=
  ((pk W).HX t).e ((pk W).jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h)

def PkVal (c : Val B →ₛₗ[B.embLL] (pk W).cX.W) : Prop :=
  ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
    ∀ h y, HasMat h y → IsUni B y → pkAt W t x h = c (val φ (latOf I (W.P.I.tup t) y))

def JVal (c : Val B →ₛₗ[B.embLL] (pk W).cX.W) (j : SmT (pk W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) : Prop :=
  ∀ w v, (pk W).prX (c w) v = pairVal B (j v) w

end GlobalTheory.TopVal

end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem period_single (l : I.Laws) (u : B.Word) (a : I.ι) (φ : Frm I a) (G : (I.per l u a).Mt) (hG : HasVal l u φ G)
    (c : (I.stX a).Cl) (z : (GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1)) → ℂ) (w : (I.per l u a).Wrow)
    (hw : w c = z) (hw' : ∀ c', c' ≠ c → w c' = 0) :
    (Nat.card ((I.stX a).Stab c) : ℂ) * (I.per l u a).period w G =
      pairVal B z (val φ (toRow I.sel (I.tup a) ((I.stX a).rep c).1.1)) := by
  letI := (I.perIn u a).clFin (l.per u a)
  have e : (I.per l u a).period w G = ∑ c' : (I.perIn u a).S'.Cl, (I.perIn u a).wt c' * pairB (K := ℂ) (I.perIn u a).sgT
      (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT)
        (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (w c')) ((I.perIn u a).rd B.fields.emb B.embLL G c') := by
    show ((∑ c' : (I.perIn u a).S'.Cl, _ : _ →ₗ[ℂ] _ →ₗ[ℂ] ℂ) w) G = _
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    rfl
  rw [e, Finset.sum_eq_single (show (I.perIn u a).S'.Cl from c)]
  · have hs : (I.perIn u a).sgT = B.wts.sgTrue := rfl
    have h1 : (I.perIn u a).rd B.fields.emb B.embLL G c =
        MvPolynomial.map B.embLL (val φ (toRow I.sel (I.tup a) ((I.stX a).rep c).1.1)).1 := hG _
    haveI : Finite ((I.stX a).Stab c) := (l.per u a).step.fin_stab c.1 _
    have h2 : (Nat.card ((I.stX a).Stab c) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h3 : (Nat.card ((I.stX a).Stab c) : ℂ) * (I.perIn u a).wt c = 1 := mul_inv_cancel₀ h2
    rw [← mul_assoc]
    refine (congrArg (· * _) h3).trans ((one_mul _).trans ?_)
    subst hw
    exact congrArg _ h1
  · intro c' _ hc
    rw [hw' c' hc, map_zero, map_zero, LinearMap.zero_apply, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)

set_option maxHeartbeats 1000000 in

theorem reads_of_val (hC : I.StdC l Z W.R.T.cols) (hW : GlobalTheory.AdForm.TwStd W) (u : B.Word)
    (j : SmT (pk W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) (a : (I.rec7 l Z).what₂.Tup) (φ : Frm I a)
    (G : (I.rec7 l Z).what₂.Amb a) (hG : RecVal u a φ G)
    (f : SmT (pk W).MX →ₗ[ℂ] (GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → ℂ))
    (hf : ∀ h y (p : XPt (B.primes X) B.R I.sel (I.tup a)) v, HasMat h y → TC.PtOf y p →
      f v h = pairVal B (j v) (val φ (toRow I.sel (I.tup a) p))) :
    Reads W u j 1 a G f := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    intro c v g hg
    have s := hC u
    rw [mul_one, hf g _ _ v hg (s.what₂.pt c)]
    have e := fun c' y => (s.eW ((W.R.T.cols.forms u).valP.eW.symm (Pi.single c (j v))) c' y y rfl).symm
    simp only [LinearEquiv.apply_symm_apply] at e
    refine (period_single l u I.mu0 φ _ (hG.1 rfl) c (j v) _ (funext fun y => (e c y).trans ?_)
      fun c' hc => funext fun y => (e c' y).trans ?_).symm
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
      rfl
  · obtain ⟨l0, t, he, ht, -, -, s⟩ := hW
    have key : ∀ (Tw : TwForms (I.rec7 l Z)) (t' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes W.R.T.n.tp W.R.T.cols Tw), Tw = I.tw l l0 Z → HEq t' t →
        ReadsG (t'.pt.cls u a h) (t'.pt.val u a h).eW j 1 (((I.rec7 l Z).eMtTw u a).symm G) f := by
      rintro _ t' rfl rfl
      intro c v g hg
      rw [mul_one, hf g _ _ v hg ((s.what₂ u a h).pt c)]
      have e := fun c' y => (s.eW u a h ((t'.pt.val u a h).eW.symm (Pi.single c (j v))) c' y y rfl).symm
      simp only [LinearEquiv.apply_symm_apply] at e
      refine (period_single l u a φ _ hG.2 c (j v) _ (funext fun y => (e c y).trans ?_)
        fun c' hc => funext fun y => (e c' y).trans ?_).symm
      · rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
        rfl
    exact key _ _ he ht

end GlobalTheory.TopVal

end
