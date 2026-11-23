import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceSubgroupIndicatorWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTwistedConstantTermMatchesStatement

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.Bc.ArchbcB.B

def M1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ w : Pl E, ¬ IsSplitAt w → ∀ n a b : ℕ, a + b = n →
      Match n a b w 1 ((KL n w : Set (UL n w)).indicator 1)
        ((((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set _).indicator 1)

def M2 : Prop := type_of% GlobalTheory.T.congruence_subgroup_indicator_weight

def M3 : Prop := type_of% GlobalTheory.T.splitPlace_twistedConstantTerm_matches

def lOf {n : ℕ} (x : Fin n → ℤ) (i : Fin (n / 2)) : ℤ :=
  x ⟨i.val, by omega⟩ - x ⟨n - 1 - i.val, by omega⟩

def symIdx (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n =>
    (∃ h : i.val < n / 2, (⟨i.val, h⟩ : Fin (n / 2)) ∈ s) ∨
      (∃ h : n - 1 - i.val < n / 2, (⟨n - 1 - i.val, h⟩ : Fin (n / 2)) ∈ s) ∨ (mid ∧ n % 2 = 1 ∧ i.val = n / 2)

def restr {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (h : S.card = m) : Fin m → ℤ :=
  fun j => x (S.orderEmbOfFin h j)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def phiX (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (x : Fin n → ℤ) (a : ℕ)
    (y : GLw a w × GLw (n - a) w) : ℂ :=
  ∑ s : Finset (Fin (n / 2)),
    if _h : s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2 then
      if h₁ : (symIdx n (a % 2 = 1) s).card = a then
        if h₂ : (symIdx n ((n - a) % 2 = 1) sᶜ).card = n - a then
          (-qh w) ^ (-vRes n a (lOf x) s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ *
            ((iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) : ℕ) * ((iwGL (n - a) w).relIndex (GlobalTheory.LFun.KGL w (n - a)) : ℕ) *
            dcos a w (tdiag ϖ (restr x _ h₁)) y.1 * dcos (n - a) w (tdiag ϖ (restr x _ h₂)) y.2
        else 0
      else 0
    else 0

def M4 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ w : Pl E, ¬ IsSplitAt w → ∀ (n a : ℕ), a ≤ n → ∀ (b : GLw n w), IsWitt n w b →
    ∀ ϖ : (w.adicCompletion E)ˣ, IsUnifAt ϖ → ∀ x : Fin n → ℤ, StrictAnti x → Cone (lOf x) →
      Match n a (n - a) w 1 (fU n w b ϖ (lOf x)) (phiX n w b ϖ x a) ∧ RegAt2 a (n - a) w (phiX n w b ϖ x a)

end PositivityTheory.Rg.Bc.ArchbcB.B
