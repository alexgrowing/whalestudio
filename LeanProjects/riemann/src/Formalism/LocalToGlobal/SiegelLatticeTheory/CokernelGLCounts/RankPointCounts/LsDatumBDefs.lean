import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Local

variable {D : Formalism.BasicNotions.D7}

abbrev MatP (D : Formalism.BasicNotions.D7) (p : PlF D) : Type :=
  Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ)

def kkOrb (p : PlF D) (Y : MatP D p) : Set (MatP D p) :=
  {Y' | ∃ l ρ : MatP D p, Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧ Y' = l * Y * ρ}

def IntP (p : PlF D) (Y : MatP D p) : Prop := ∀ a b, Y a b ∈ (M p).R

def InOrbP (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Prop :=
  ∃ w₀, modPt δ T T' p w = some w₀ ∧
    ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
      Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2

def phL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℂ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    if h : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
        Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 then
      dfac M δ T T' p w *
        (M p).psiR (Loc.simpleLow (Loc.uLow h.choose.1) + Loc.simpleUp (Loc.uUp w₀ h.choose.2))
    else 0

def wtL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℝ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    (((Measure.pi fun _ : Loc.IL (D.R.rS + 1) => (M p).mu).prod (Measure.pi fun _ : Loc.IN w₀ => (M p).mu))
      {xy | Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y}).toReal

def thL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Option ((M p).Cls D.R.rS) :=
  clsOf (M p) (Y + Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0)

def nIsoO (p : PlF D) (o o' : Option ((M p).Cls D.R.rS)) : ℕ :=
  match o, o' with
  | some c, some c' => (M p).nIso (Quotient.out c) (Quotient.out c')
  | _, _ => 0

def IsLCls (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : Prop :=
  ∃ Y, IntP M p Y ∧ InOrbP δ T T' p w Y ∧ O = kkOrb M p Y

def repL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : MatP D p :=
  if h : IsLCls M δ T T' p w O then h.choose else 0

def fL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ) *
      (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ)
  else 0

def gL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def hL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def kL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ) else 0

def eL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then 1 else 0

def sgnP (p : PlF D) : MatP D p := Matrix.diagonal fun b : Fin (D.R.rS + 1) => (-1) ^ (D.R.rS - b.val)

def x0L (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : Set (MatP D p) := kkOrb M p (modMat δ T T' p w)

end Local

section Glob

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def nrep (γ : TermDef.Term D u u' F0 what₂) :
    Option (Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D) :=
  if h : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 then some h.choose else none

def zT (γ : TermDef.Term D u u' F0 what₂) : PairVal.MatR D :=
  match nrep γ with
  | some x => ZhatL (lf D F0) x.2.1
  | none => 0

def ptT (γ : TermDef.Term D u u' F0 what₂) : Point D.host.E (D.R.rS + 1) :=
  match nrep γ with
  | some x => x.1
  | none => PairVal.junkPoint D u u'

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)

def thT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Option ((M p).Cls D.R.rS) :=
  thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ))

def locT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Set (MatP D p) :=
  kkOrb M p (CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p)

def dnT (L : CntLocal.LocSp D M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (γ : TermDef.Term D u u' F0 what₂) : ℝ :=
  ∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') (zT γ) p

end Glob

end Formalism.L2.SG.LsDatumB
