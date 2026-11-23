import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2.NG

section lvl

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def ParaRT (s : SplitPlace L) (r : ℕ) (h : GL (Fin n) (s.v.adicCompletion L⁺)) : Prop :=
  h ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring ∧
    ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v (h.val a b) < 1

def UniRT (s : SplitPlace L) (r : ℕ) (h : GL (Fin n) (s.v.adicCompletion L⁺)) : Prop :=
  ParaRT s r h ∧ ∀ a b : Fin n, a.val < r → b.val < r →
    (b.val < a.val → Valued.v (h.val a b) < 1) ∧ (a = b → Valued.v (h.val a b - 1) < 1)

def detDD (s : SplitPlace L) (r : ℕ) (h : GL (Fin n) (s.v.adicCompletion L⁺)) : s.v.adicCompletion L⁺ :=
  (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => h.val a.1 b.1).det

def supDiag (s : SplitPlace L) (r : ℕ) (h : GL (Fin n) (s.v.adicCompletion L⁺)) : s.v.adicCompletion L⁺ :=
  ∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then h.val a b else 0

def IsProdLevel (J : Subgroup (GAf L n)) : Prop :=
  ∀ κ ∈ J, ∀ v, ∃ κ' ∈ J, TrivOutside {v} κ' ∧
    (κ'.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (κ.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v)

structure LevelPara (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s : SplitPlace L) (r : ℕ)
    (ξ : (s.v.adicCompletion L⁺)ˣ →* ℂˣ) : Prop where
  mem : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ ParaRT s r (s.loc n κ))
  chr : ∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → ∀ u : (s.v.adicCompletion L⁺)ˣ,
    (u : s.v.adicCompletion L⁺) = detDD s r (s.loc n κ) → χ ⟨κ, h⟩ = ξ u

structure LevelUni (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s : SplitPlace L) (r : ℕ)
    (ψ₀ : AddChar (s.v.adicCompletion L⁺) ℂ) (ξ : (s.v.adicCompletion L⁺)ˣ →* ℂˣ) : Prop where
  mem : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ UniRT s r (s.loc n κ))
  chr : ∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → ∀ u : (s.v.adicCompletion L⁺)ˣ,
    (u : s.v.adicCompletion L⁺) = detDD s r (s.loc n κ) →
    ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) = ψ₀ (supDiag s r (s.loc n κ)) * ξ u

def IsCompAt (χ : Host.HChar L) (s : SplitPlace L) (ξ : (s.v.adicCompletion L⁺)ˣ →* ℂˣ) : Prop :=
  (∃ N : ℕ, ∀ u : (s.v.adicCompletion L⁺)ˣ,
    Valued.v ((u : s.v.adicCompletion L⁺) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) ∧
  ∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion L⁺) k) = χ.locK s.w k

def IsPsi0 (s : SplitPlace L) (ψ₀ : AddChar (s.v.adicCompletion L⁺) ℂ) : Prop :=
  (∀ x, Valued.v x < 1 → ψ₀ x = 1) ∧ ∃ x, Valued.v x ≤ 1 ∧ ψ₀ x ≠ 1

end lvl

open Formalism.BasicNotions in

def paramV (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ) : Multiset ℂ :=
  (Finset.univ.val.map fun i : Fin (R.k - 1) => ((h.v i : ℚ) : ℂ) - sh) +
  (Finset.univ.val.map fun i : Fin R.m => -((h.b i : ℚ) : ℂ) - sh) +
  ((Multiset.range R.t).map fun c : ℕ => -((h.e j : ℚ) : ℂ) - sh + ((R.t : ℂ) - 1 - 2 * c) / 2)

end Formalism.L2.NG
