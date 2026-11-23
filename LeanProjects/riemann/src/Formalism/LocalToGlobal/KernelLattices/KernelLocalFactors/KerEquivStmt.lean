import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainInstY

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section LocLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def XiLaw (i : ℕ) (al : L.β i) (be : L.β (i + 1)) : Prop :=
  ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (h : ↥(L.levG i al ⟨P.1, hP⟩).H) (h' : ↥(L.levG (i + 1) be ⟨P.1, hP⟩).H)
    (κ : ↥(GLint X.E (R.N i) P.1)) (κ' : ↥(GLint X.E (R.N (i + 1)) P.1)),
    (∀ x ∈ stdAt X.E (R.N i) P.1, redV P.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV P.1 x)) →
    (∀ x ∈ stdAt X.E (R.N (i + 1)) P.1, redV P.1 (κ'.1 x) = (h'.1⁻¹).1.mulVec (redV P.1 x)) →
    ∀ y : HomE X.E (R.N i) (R.N (i + 1)),
      rhoS Ch sel mu i P (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu i P (LinearEquiv.det κ'.1 : X.Eˣ) *
          XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) =
        (((L.levG (i + 1) be ⟨P.1, hP⟩).lam h' : X.Kˣ) : X.K) * ((((L.levG i al ⟨P.1, hP⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
          XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y

end LocLaw

section LocLawPsi

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def PsiLaw (m2 : ℕ) (al : L.β m2) (b : L.β (m2 + 1)) : Prop :=
  ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (h₀ : ↥(L.levG m2 al ⟨P.1, hP⟩).H) (h : ↥(L.levG (m2 + 1) b ⟨P.1, hP⟩).H)
    (κ₀ : ↥(GLint X.E (R.N m2) P.1)) (κ : ↥(GLint X.E (R.N (m2 + 1)) P.1)),
    (∀ x ∈ stdAt X.E (R.N m2) P.1, redV P.1 (κ₀.1 x) = (h₀.1⁻¹).1.mulVec (redV P.1 x)) →
    (∀ x ∈ stdAt X.E (R.N (m2 + 1)) P.1, redV P.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV P.1 x)) →
    ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
      rhoS Ch sel mu m2 P (LinearEquiv.det κ₀.1 : X.Eˣ) * rhoT Ch sel mu m2 P (LinearEquiv.det κ.1 : X.Eˣ) *
          PsiAt Ch sel mu cst m2 P (L.h m2 al P) (κ.1.symm.toLinearMap ∘ₗ x₀ ∘ₗ κ₀.1.toLinearMap) (κ.1.symm y') =
        (((L.levG (m2 + 1) b ⟨P.1, hP⟩).lam h : X.Kˣ) : X.K) * ((((L.levG m2 al ⟨P.1, hP⟩).lam h₀)⁻¹ : X.Kˣ) : X.K) *
          PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ y'

end LocLawPsi

end Formalism.L2.Ker
