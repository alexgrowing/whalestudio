import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.QNF

open Formalism.BasicNotions Formalism.L2.DIV

def nfMat {E : Type} [Field E] (n c : ℕ) (q : E) (nn : Fin c → ℤ) (z : Fin n → E) : Matrix (Fin (n + c)) (Fin (n + c)) E :=
  fun a b =>
    if hb : b.1 < n then (if a = b then 1 else 0)
    else if hab : a = b then q ^ nn ⟨b.1 - n, by have := b.isLt; omega⟩
    else if h : b.1 = n ∧ a.1 < n then q ^ nn ⟨0, by have := b.isLt; omega⟩ * z ⟨a.1, h.2⟩ else 0

def MatNF {X : Formalism.L2.Col.Fields} (Pr : Formalism.L2.Col.Primes X) (R : Ranks) (j : ℕ) (v : HeightOneSpectrum (𝓞 X.E))
    (h : Formalism.L2.Col.AutY X R j) : Prop :=
  ∃ (nn : Fin (Formalism.L2.Col.cOf R j) → ℤ) (z : Fin (R.N j) → X.E),
    (∀ i, -(j : ℤ) ≤ nn i ∧ nn i ≤ 0) ∧
    (fun l : Fin (R.N j + Formalism.L2.Col.cOf R j) => if h : l.1 < R.N j then z ⟨l.1, h⟩ else 0) ∈
      Formalism.L2.Col.lamYat (Pr := Pr) (R := R) j v ∧
    (Formalism.L2.Col.lamYat (Pr := Pr) (R := R) j v).map (h.toLinearMap.restrictScalars (𝓞 X.E)) =
      (Formalism.L2.Col.lamYat (Pr := Pr) (R := R) j v).map
        ((Matrix.toLin' (nfMat (R.N j) (Formalism.L2.Col.cOf R j) ((Formalism.L2.Col.qOf v : ℕ) : X.E) nn z)).restrictScalars (𝓞 X.E))

def IdxMatNF {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} {Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (L : Formalism.L2.Col.ChIdx X Pr R Q) : Prop :=
  ∀ (j : ℕ) (b : L.β j) (v : ↥(Formalism.L2.Col.uSG Pr.vGs Q)), v.1 ∉ Pr.vGs → 1 ≤ j → j + 2 ≤ R.m → MatNF Pr R j v.1 (L.h j b v)

end GlobalTheory.QNF

end
