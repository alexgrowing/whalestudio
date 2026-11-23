import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColInst

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

def Amb.EOmega {X : Fields} (A : Amb X) (a b : ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' → ContDiff ℂ ⊤ (A.e a b N N')

def Amb.IndOmega {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ContDiff ℂ ⊤ (A.thInd Sall N N' c x)

def WtLaw {ι : Type} {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (e : ι → ℤ) : Prop :=
  (∀ τ, (n τ : ℤ) + ((b / 2 : ℕ) : ℤ) - e τ = (lam τ).detShift) ∧ ∀ τ, e τ - ((a / 2 : ℕ) : ℤ) = -(lam' τ).detShift

def Amb.EqLaw {X : Fields} (A : Amb X) (a b : ℕ) : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ z, A.e a b (gmap γ.1 N) (gmap γ'.1 N') z = A.e a b N N' (A.pullV a b γ.1 γ'.1 z)

def ThIndOfEq : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ),
    (∀ τ x, X.embC A.σ₀ τ (star x) = star (X.embC A.σ₀ τ x)) → 0 < D → A.LaHyp a b Sall → A.EqLaw a b → A.ThIndEq a b Sall D

end Formalism.L2.Ker
