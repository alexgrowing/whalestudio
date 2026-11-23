import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivStmt
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Law

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

open Classical in

def XiLawQ (i : ℕ) (al : L.β i) (be : L.β (i + 1)) : Prop :=
  ∀ (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (c : ↥(L.levQ i al ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H)
    (c' : ↥(L.levQ (i + 1) be ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H)
    (y : HomE X.E (R.N i) (R.N (i + 1))),
      rhoS Ch sel mu i w (LinearEquiv.det (c.1⁻¹).1 : X.Eˣ) * rhoT Ch sel mu i w (LinearEquiv.det (c'.1⁻¹).1 : X.Eˣ) *
          XiAt Ch sel mu cst i w (L.h i al w) (L.h (i + 1) be w) (c'.1.1.toLinearMap ∘ₗ y ∘ₗ (c.1⁻¹).1.toLinearMap) =
        (((L.levQ (i + 1) be ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam c' : X.Kˣ) : X.K) *
          ((((L.levQ i al ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam c)⁻¹ : X.Kˣ) : X.K) *
          XiAt Ch sel mu cst i w (L.h i al w) (L.h (i + 1) be w) y

open Classical in

def PsiLawQ (m2 : ℕ) (al : L.β m2) (b : L.β (m2 + 1)) : Prop :=
  ∀ (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (c₀ : ↥(L.levQ m2 al ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H)
    (c : ↥(L.levQ (m2 + 1) b ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H)
    (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
      rhoS Ch sel mu m2 w (LinearEquiv.det (c₀.1⁻¹).1 : X.Eˣ) * rhoT Ch sel mu m2 w (LinearEquiv.det (c.1⁻¹).1 : X.Eˣ) *
          PsiAt Ch sel mu cst m2 w (L.h m2 al w) (c.1.1.toLinearMap ∘ₗ x₀ ∘ₗ (c₀.1⁻¹).1.toLinearMap) (c.1.1 y') =
        (((L.levQ (m2 + 1) b ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam c : X.Kˣ) : X.K) *
          ((((L.levQ m2 al ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam c₀)⁻¹ : X.Kˣ) : X.K) *
          PsiAt Ch sel mu cst m2 w (L.h m2 al w) x₀ y'

structure KerLaws (P : LevFam X.E X.K R.r Pr.vGs) (m2 : ℕ) (b : L.β (m2 + 1)) : Prop where
  xi : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)), XiLaw Ch sel mu cst L i al be
  xiQ : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)), XiLawQ Ch sel mu cst L i al be
  psi : ∀ al : L.β m2, PsiLaw Ch sel mu cst L m2 al b
  top : TopLaw Ch sel mu cst L P m2 b

end Law

end Formalism.L2.Ker
