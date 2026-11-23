import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KZ

def ZetaSysUr2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl), Sys W c y S' ∧ NzAt W A y

theorem zetaElementsUnramifiedOrdinary_of_eulerSystem_inertia (h : ZetaSysUr2) : ZetaUr := fun l _ Ω _ _ _ ι e S A W g hN hS => es_of_sys (h l Ω ι e S A W g hN hS)

def ExistsZetaEulerSystemIwasawaData (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω → (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' ∧ IwSys2 c A ν Z ∧ SpLink A e χ Z y ∧ Pin e A W c ν χ Z

def ZetaEulerSystemNonvanishing (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∀ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω → (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' → IwSys2 c A ν Z → SpLink A e χ Z y → Pin e A W c ν χ Z → NzAt W A y

theorem zetaSysU_of_halves2 (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : ExistsZetaEulerSystemIwasawaData Pin) (hL : ZetaEulerSystemNonvanishing Pin) : ZetaSysUr2 := by
  intro l _ Ω _ _ _ ι e S A W g hN hS
  obtain ⟨c, y, S', ν, χ, Z, h1, h2, h3, h4⟩ := hG l Ω ι e S A W g hN hS
  exact ⟨c, y, S', h1, hL l Ω ι e S A W g hN hS c y S' ν χ Z h1 h2 h3 h4⟩

theorem zetaUr_of_halves2 (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : ExistsZetaEulerSystemIwasawaData Pin) (hL : ZetaEulerSystemNonvanishing Pin) : ZetaUr :=
  zetaElementsUnramifiedOrdinary_of_eulerSystem_inertia (zetaSysU_of_halves2 Pin hG hL)

end GlobalTheory.KZ

end
