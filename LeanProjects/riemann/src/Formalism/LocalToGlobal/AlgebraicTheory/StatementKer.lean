import Formalism.LocalToGlobal.AlgebraicTheory.StatementD
import Formalism.LocalToGlobal.KernelLattices.ThDistC

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH IsSelfDual IsLat Th alphaQ)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.GD (LocNorm InMul frameM)
open Formalism.L2.Col (Fields Sp HomE homAt divLat)
open Formalism.L2.Ker (Amb DVar VCx LamC)

section Flat

variable (T : Type) (a b : ℕ)

def flat : (DVar T a b → ℂ) ≃ₗ[ℂ] VCx T a b where
  toFun z := fun τ i j => z (τ, i, j)
  invFun w := fun k => w k.1 k.2.1 k.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def hSc [DecidableEq T] (sc : ℝ) : Matrix (DVar T a b) (DVar T a b) ℂ := Matrix.diagonal fun _ => (sc : ℂ)

end Flat

section Std

variable {X : Fields} (A : Amb X) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

def lamF : AddSubgroup (DVar X.Tau a b → ℂ) :=
  (LamC (X.embC A.σ₀) A.δ A.AA N N').comap (flat X.Tau a b).toLinearMap.toAddMonoidHom

def thF : (DVar X.Tau a b → ℂ) → ℂ := fun z => A.e a b N N' (flat X.Tau a b z)

def KerStd (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  CmOK a₀ b₀ c₀ A.d ∧ 0 < A.sc ∧ IsLat (lamF A N N') ∧ IsSelfDual (matH (hSc X.Tau a b A.sc)) (lamF A N N') ∧
  (∀ x ∈ lamF A N N', Formalism.L2.Th1.F.cmTheta b₀ A.d • x ∈ lamF A N N') ∧
  thF A N N' ∈ Th (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (lamF A N N') ∧
  IntCurve (curveL p (cmL a₀ b₀ A.d ha hd lam hlam) ι) ∧
  LocNorm a₀ b₀ A.d ha hd lam hlam (hSc X.Tau a b A.sc) (lamF A N N') (thF A N N') p ι ∧
  (∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau a b → ℂ) (M : J → DVar X.Tau a b → ℂ_[p]),
    (∀ j, InMul (cmL a₀ b₀ A.d ha hd lam hlam) (lamF A N N') (v j)) ∧ (∀ j k, ‖M j k‖ ≤ 1) ∧
    ∀ i k, frameM (ι : ℂ →+* ℂ_[p]) v M i k = if i = k then ι (A.cD k.1) else 0) ∧
  ‖ι (A.chiF a b N N')‖ = 1

def SplitS (S : Finset (HeightOneSpectrum (𝓞 X.E))) (p : ℕ) (π : ℂ) (pE : 𝓞 X.E) : Prop :=
  (∀ τ, X.embC A.σ₀ τ (pE : X.E) = π) ∧ (∀ τ, X.embC A.σ₀ τ (star (pE : X.E)) = conj π) ∧
  ∀ P : HeightOneSpectrum (𝓞 X.E), (p : 𝓞 X.E) ∈ P.asIdeal → (P ∈ S ↔ pE ∉ P.asIdeal)

end Std

def JetAtSplit : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
    p ≠ 2 → ¬ p ∣ A.d → KerStd A N N' a₀ b₀ c₀ ha hd lam hlam p ι →
    Formalism.L2.Col.IsSdLat N → Formalism.L2.Col.IsSdLat N' → A.LaHyp a b S →
  ∀ (π : ℂ) (pE : 𝓞 X.E), IsQInt A.d π → π * conj π = (p : ℂ) → SplitS A S p π pE →
  ∀ (c' : ℕ) (x : HomE X.E a b), 0 < c' → ¬ p ∣ c' → x ∈ divLat c' (homAt S N N') →
  ∀ m : DVar X.Tau a b →₀ ℕ,
    ‖ι (A.σ₀ (A.jetK S N N' (p * c') x m))‖ * ‖ι (conj π)‖ ^ m.degree * ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) ≤ 1

def JetAtPlace : Prop :=
  ∀ (X : Fields) (σ₀ : X.K →+* ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 X.K)),
    0 < Formalism.DivisionValues.vw w (p : X.K) →
    (∀ y : X.K, y ≠ 0 → ‖ι (σ₀ y)‖ = (p : ℝ) ^ (-(Formalism.DivisionValues.vw w y : ℝ) / (Formalism.DivisionValues.vw w (p : X.K) : ℝ))) →
  ∀ (y pb : X.K) (D R : ℕ), pb ≠ 0 → ‖ι (σ₀ y)‖ * ‖ι (σ₀ pb)‖ ^ D * ‖(p : ℂ_[p])‖ ^ R ≤ 1 →
    y = 0 ∨ -((D : ℤ) * Formalism.DivisionValues.vw w pb) - (R : ℤ) * Formalism.DivisionValues.vw w (p : X.K) ≤ Formalism.DivisionValues.vw w y

end Formalism.L2.AlgTh
