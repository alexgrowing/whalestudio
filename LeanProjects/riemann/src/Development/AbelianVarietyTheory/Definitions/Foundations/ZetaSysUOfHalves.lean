import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KZ

def ZetaSysUr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl), Sys W c y S' ∧ NzAt W A y

theorem zetaUr_of_sys (h : ZetaSysUr) : ZetaUr := fun l _ Ω _ _ _ ι e S A W g hN hS => es_of_sys (h l Ω ι e S A W g hN hS)

def GlobU (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω →* (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω →* (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' ∧ IwSys c A ν Z ∧ SpLink A e χ Z y ∧ Pin e A W c ν χ Z

def LocU (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω →* (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∀ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω →* (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' → IwSys c A ν Z → SpLink A e χ Z y → Pin e A W c ν χ Z → NzAt W A y

theorem zetaSysU_of_halves (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω →* (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : GlobU Pin) (hL : LocU Pin) : ZetaSysUr := by
  intro l _ Ω _ _ _ ι e S A W g hN hS
  obtain ⟨c, y, S', ν, χ, Z, h1, h2, h3, h4⟩ := hG l Ω ι e S A W g hN hS
  exact ⟨c, y, S', h1, hL l Ω ι e S A W g hN hS c y S' ν χ Z h1 h2 h3 h4⟩

theorem zetaUr_of_halves (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω →* (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : GlobU Pin) (hL : LocU Pin) : ZetaUr :=
  zetaUr_of_sys (zetaSysU_of_halves Pin hG hL)

end GlobalTheory.KZ

end
