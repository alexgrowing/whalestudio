import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw

variable (D : D7)

def SupG : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b g, ∀ f ∈ D.nexp.Bsup i j b,
  D.nexp.actG i j b g f ∈ D.nexp.Bsup i j b

def SupFull : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (D.nexp.Bsup i j b).FG ∧
  Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) = ⊤

def SupHk : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ f ∈ D.nexp.Bsup i j b,
  D.nexp.hkF i j b k P f ∈ D.nexp.Bsup i j b

def UnivSup (E : XD D) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M,
  (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (D.ntw.S0 i) → Disjoint Q (D.nexp.lev i j b a) →
  ∃ Xi : DelQM D.host (D.ntw.l i) Q M →₀ D.nexp.Fm i j b,
    D.nexp.thU i j b Q M a = Xi.sum (fun δ f => f ⊗ₜ[D.ntw.O i] AddMonoidAlgebra.single δ (1 : D.ntw.O i)) ∧
    ∀ δ, Xi δ ∈ Fm0 D.nexp i j b ∧ ((D.ntw.l i : D.ntw.O i) ^ c) • Xi δ ∈ D.nexp.Bsup i j b

def HkComm : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P k' P', HkIdx i k P → HkIdx i k' P' →
  Commute (D.nexp.hkF i j b k P) (D.nexp.hkF i j b k' P')

def OffRange : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → (∀ j, j ∉ Finset.Icc 1 D.R.m → ∀ b, Subsingleton (D.nexp.Fm i j b)) ∧
  ∀ s P, D.ntw.hEig i s 0 P = 1

def HkSS : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
  V0 D.nexp i j b ≤ ⨆ ev, (Eigsp D.nexp i j b ev ⊓ V0 D.nexp i j b)

end GlobalTheory.SupLaw
