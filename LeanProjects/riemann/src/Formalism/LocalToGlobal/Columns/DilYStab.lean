import Formalism.LocalToGlobal.Columns.DecoratedFrameDiagonalTwistDecoration

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Pairs

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 j : ℕ}

variable (W cst L u m2 j) in

abbrev PtY (b : L.β j) : Type := (cplAt W sel mu cst L u m2 j b).Pts

@[reducible] def ptYAct (b : L.β j) : MulAction ((chFY W sel mu cst L u m2 j).mem b).G (PtY W cst L u m2 j b) := ((chFY W sel mu cst L u m2 j).mem b).actD

attribute [local instance] ptYAct

def PtY.deco {b : L.β j} (x : PtY W cst L u m2 j b) : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs := x.1.1.deco

theorem sameOn_QE {d d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs} (h : DecoSet.SameOn (rowSG Pr sel mu) d d') :
    DecoSet.SameOn (QE sel (mu : Chr X.F X.E X.K)) d d' := by
  classical
  exact fun P hP => h P (Finset.mem_union_right _ hP)

theorem cplAt_ys_mv (b : L.β j) (p : ChPt (R := R) sel mu u j) {d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs}
    (h : DecoSet.SameOn (rowSG Pr sel mu) p.deco d') :
    (cplAt W sel mu cst L u m2 j b).ys (p.mv d') = (cplAt W sel mu cst L u m2 j b).ys p := by
  classical
  show (if j = m2 + 1 then ybSet sel mu cst (p.mv d').deco.1.N else {Set.univ}) = if j = m2 + 1 then ybSet sel mu cst p.deco.1.N else {Set.univ}
  rw [DecoF.mv_deco (sameOn_QE h)]
  split_ifs
  · exact ybSet_sameAt sel mu cst h
  · rfl

def PtY.repl {b : L.β j} (x : PtY W cst L u m2 j b) (d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs)
    (h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : PtY W cst L u m2 j b :=
  ⟨(x.1.1.mv d', x.1.2), by rw [cplAt_ys_mv b x.1.1 h]; exact x.2⟩

open Classical in

def PtY.mv {b : L.β j} (x : PtY W cst L u m2 j b) (d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) : PtY W cst L u m2 j b :=
  if h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d' then x.repl d' h else x

theorem PtY.mv_pos {b : L.β j} {x : PtY W cst L u m2 j b} {d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs}
    (h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : x.mv d' = x.repl d' h := dif_pos h

theorem PtY.mv_neg {b : L.β j} {x : PtY W cst L u m2 j b} {d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs}
    (h : ¬ DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : x.mv d' = x := dif_neg h

theorem PtY.mv_deco {b : L.β j} {x : PtY W cst L u m2 j b} {d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs}
    (h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : (x.mv d').deco = d' := by
  rw [PtY.mv_pos h]
  exact DecoF.mv_deco (sameOn_QE h)

def grpDeco {b : L.β j} (g : ((chFY W sel mu cst L u m2 j).mem b).G) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs := (g.1, g.2.1.1)

theorem PtY.mv_smul {b : L.β j} (g : ((chFY W sel mu cst L u m2 j).mem b).G) (x : PtY W cst L u m2 j b)
    (d' : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) :
    PtY.mv (((chFY W sel mu cst L u m2 j).mem b).actD.toSMul.smul g x) (grpDeco g • d') =
      ((chFY W sel mu cst L u m2 j).mem b).actD.toSMul.smul g (x.mv d') := by
  by_cases h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d'
  · rw [PtY.mv_pos h, PtY.mv_pos (show DecoSet.SameOn (rowSG Pr sel mu)
      (PtY.deco (((chFY W sel mu cst L u m2 j).mem b).actD.toSMul.smul g x)) (grpDeco g • d') from h.smul _)]
    apply Subtype.ext
    apply Prod.ext
    · exact DecoF.mv_smul (FrmG.incl (L.levG j b) (L.levQ j b) g) x.1.1 d'
    · rfl
  · rw [PtY.mv_neg h, PtY.mv_neg (fun h' : DecoSet.SameOn (rowSG Pr sel mu)
      (PtY.deco (((chFY W sel mu cst L u m2 j).mem b).actD.toSMul.smul g x)) (grpDeco g • d') => h (DecoSet.SameOn.of_smul _ h'))]

def PtY.dia1 {b : L.β j} (P : {P // P ∈ Pr.vT u}) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (x : PtY W cst L u m2 j b) : PtY W cst L u m2 j b :=
  ⟨(x.1.1.dia1 P a, x.1.2), x.2⟩

def PtY.upL {b : L.β j} (x : PtY W cst L u m2 j b) (P : {P // P ∈ Pr.vT u}) (q : 𝓞 X.E) (y : x.deco.lv P) : PtY W cst L u m2 j b :=
  x.mv (x.deco.upL P q y)

def PtY.dnL {b : L.β j} (x : PtY W cst L u m2 j b) (P : {P // P ∈ Pr.vT u}) (g : Module.Dual (𝓞 X.E ⧸ P.1.asIdeal) (x.deco.lk P)) :
    PtY W cst L u m2 j b :=
  x.mv (x.deco.dnL P g)

def OffBad (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mu : Tup X.F X.E X.K S) (P : HeightOneSpectrum (𝓞 X.E)) : Prop :=
  conjPrime₂ P ≠ P ∧ ∀ P' ∈ rowSG Pr sel mu, P' ≠ P ∧ P' ≠ conjPrime₂ P

def classRepresentativePair (c : (chFY W sel mu cst L u m2 j).Cl) : PtY W cst L u m2 j c.1 := ((chFY W sel mu cst L u m2 j).mem c.1).outSec.rep c.2

def clsY (b : L.β j) (x : PtY W cst L u m2 j b) : (chFY W sel mu cst L u m2 j).Cl := ⟨b, ((chFY W sel mu cst L u m2 j).mem b).cls x⟩

def dilY (P : {P // P ∈ Pr.vT u}) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (c : (chFY W sel mu cst L u m2 j).Cl) : (chFY W sel mu cst L u m2 j).Cl :=
  clsY c.1 ((classRepresentativePair c).dia1 P a)

end Pairs

end Formalism.L2.Col
