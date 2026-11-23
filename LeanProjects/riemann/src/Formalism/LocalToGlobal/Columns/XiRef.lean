import Mathlib
import Formalism.LocalToGlobal.Columns.ChainInstY

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Yb

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.yOf (d : Deco E n ST SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) : Set (Sp E n) :=
  {z | ∀ w : SG, (qOf w.1 : E) • z ∈ d.at w.1 ∧ d.be w ((qOf w.1 : E) • z) = v w}

def Deco.y0 (d : Deco E n ST SG) (k : ℕ) : Set (Sp E n) := d.yOf fun w => Loc.eN (𝓞 E ⧸ w.1.asIdeal) n k

end Yb

section Ref

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

variable {sel mu} in

def liftQ (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet X.E n ST SG) :
    DecoF X.E n ST SG (QE sel (mu : Chr X.F X.E X.K)) :=
  ⟨(p, fun _ => 1), fun P _ => absurd (hQ ▸ P.2 : P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 X.E)))) (Finset.notMem_empty _)⟩

def XiRef {u : Pr.Word} (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (i : ℕ) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if h : i < m2 then XiEntry Ch sel mu cst L i (al i (by omega)) (al (i + 1) (by omega)) p p' x
  else if h' : i = m2 then XiCpl1 Ch sel mu cst L i (al i (by omega)) p p' (p'.deco.1.y0 R.k) x
  else if i = m2 + 1 then XiTop Ch sel mu cst i p (p.deco.1.y0 R.k) p' x
  else 0

def refK {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2) (al : ∀ j, j ≤ m2 + 1 → L.β j) (i : ℕ) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) :
    (colValF W sel mu u i).V →ₗ[X.K] (colValF W sel mu u (i + 1)).V :=
  kerOf (T.th i) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
    p'.deco.1.N (frsF sel mu p') (XiRef Ch sel mu cst L m2 al i p p')

end Ref

end Formalism.L2.Col
