import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Pos

variable {X : Fields} (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

def QSep : Prop := ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs

def QUnif : Prop := ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2

end Pos

section Law

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

open Classical in

def TopLawQ (P : LevFam X.E X.K R.r Pr.vGs) (m2 : ℕ) (b : L.β (m2 + 1)) : Prop :=
  ∀ (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (c : ↥(L.levQ (m2 + 1) b ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H)
    (h₁ : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) (hh₁ : h₁ w ∈ ((rowTy Ch sel mu P).inv w).H)
    (κr : ↥(GLint X.E (R.N R.m - 1) w.1)) (κt : ↥(GLint X.E (R.N R.m) w.1)),
    (∀ x ∈ stdAt X.E (R.N R.m - 1) w.1, redV w.1 (κr.1 x) = ((h₁ w)⁻¹).1.mulVec (redV w.1 x)) →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (κt.1 x) = ((extGH (N_m_succ R) h₁ w)⁻¹).1.mulVec (redV w.1 x)) →
    ∀ y : HomE X.E (R.N (m2 + 1)) (R.N R.m - 1),
      rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det (c.1⁻¹).1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κt.1 : X.Eˣ) *
          PhiTop Ch mu cst.sharp m2 w.1 (κr.1.symm.toLinearMap ∘ₗ y ∘ₗ (c.1⁻¹).1.toLinearMap ∘ₗ
            LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        (((((rowTy Ch sel mu P).inv w).lam ⟨h₁ w, hh₁⟩)⁻¹ : X.Kˣ) : X.K) *
          ((((L.levQ (m2 + 1) b ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam c)⁻¹ : X.Kˣ) : X.K) *
          PhiTop Ch mu cst.sharp m2 w.1 (y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))

end Law

end Formalism.L2.Ker
