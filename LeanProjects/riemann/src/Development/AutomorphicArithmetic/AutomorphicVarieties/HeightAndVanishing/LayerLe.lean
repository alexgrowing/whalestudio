import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

def lossAll (l N n e : ℕ) : ℕ := Chr.loss l N n e + N.primeFactors.card * n.factorization l

def LayerLe (χ : PChar) (l : ℕ) [Fact l.Prime] (j t : ℕ) (B : ℝ) : Prop :=
  ∀ (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField (Lchi χ l) L₀ →
    ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l j L₀ L₁ → VVat l L₁ t B

def CountIV : Prop :=
  ∀ (χ : PChar) (l : ℕ) [Fact l.Prime] (j : ℕ), l ∈ Bchi χ → ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ B : ℝ, LayerLe χ l j t B → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (c : Coef l)
      (ψ : DirichletCharacter c.O h.N), h.IsChar ψ → Odd (orderOf (chiP l ψ)) →
        Chr.SumLe l c.O (fun e => Vlen Ω c e ψ) t (B + ((h.N : ℝ) * t) ^ C)

def PlusLe {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (S : Finset Nat.Primes) (t : ℕ) (B : ℝ) : Prop :=
  (∀ l ∈ S, ∀ e : ℕ, 0 < e → e < t → plusLen (ld l) e ≠ ⊤) ∧
    ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ) ≤ B

def SumIn : Prop :=
  ∀ (χ : PChar) (l : Nat.Primes) (j : ℕ), (l : ℕ) ∈ Bchi χ → ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ B : ℝ, 0 ≤ B → LayerLe χ l j t B → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField χ h.ex h.q1 h.d E →
      ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
        PlusLe ld {l} t (((h.N : ℝ) * t) ^ C + C * B)

def SumOut : Prop :=
  ∀ χ : PChar, ∃ (C r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = χ → r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d →
    ∀ t : ℕ, 2 ≤ t → h.Big t → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField χ h.ex h.q1 h.d E →
      ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p)
        (S : Finset Nat.Primes), (∀ l ∈ S, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∉ Bchi χ) → PlusLe ld S t (((h.N : ℝ) * t) ^ C)

def PointHV : Prop :=
  ∀ (χ : PChar) (j : ℕ → ℕ), ∃ (C r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = χ →
    r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d → ∀ t : ℕ, 2 ≤ t → h.Big t → ∀ B : ℝ, 0 ≤ B →
      (∀ l ∈ Bchi χ, ∀ [Fact l.Prime], LayerLe χ l (j l) t B) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField χ h.ex h.q1 h.d E →
        VVplusLe E t (((h.N : ℝ) * t) ^ C + C * B)

end UpperTheory.V.HV

end
