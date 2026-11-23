import Formalism.PieriBlockIdeals.StatementLP
import Formalism.PieriBlockIdeals.StatementLR

open MvPolynomial

namespace Formalism.CohomologicalDescent.LPR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample Formalism.CohomologicalDescent.LP Formalism.CohomologicalDescent.LR

def DiagTransfer : Prop :=
  ∀ (K M A : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A] (i : M →ₗ[K] A)
    (g : Module.End K M) (f : Module.End K A), Function.Injective i → (∀ x, i (g x) = f (i x)) →
    (⨆ μ : K, Module.End.eigenspace f μ) = ⊤ → (⨆ μ : K, Module.End.eigenspace g μ) = ⊤

def IrredGen : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N), FormMod T B → ∀ h : N, h ≠ 0 →
    (∀ Z : Submodule K N, Stab T Z → Z ≠ ⊥ → h ∈ Z) → ∀ S : Submodule K N, Stab T S → h ∈ S → S = ⊤

def EulerDiag : Prop :=
  ∀ (r n : ℕ) (a : Fin r), (⨆ μ : ℚ, Module.End.eigenspace (der r n a a : Module.End ℚ (MvPolynomial (Fin r × Fin n) ℚ)) μ) = ⊤

def RealFinite : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ), FiniteDimensional ℚ ↥(dualWeyl ℚ r n ν)

def RealFormMod : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ),
    FormMod (rationalBlockModuleSetting p q w lam2).EW ((formB p q w lam2).restrict (rationalBlockModuleSetting p q w lam2).W)

def RealHW : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Antitone lam2 → (∀ b, lam2 b ≤ w) → ∀ h : (rationalBlockModuleSetting p q w lam2).W,
    ((h : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = hw ℚ le_rfl (LD.blockWt p q w lam2) →
    h ≠ 0 ∧ IsHW (rationalBlockModuleSetting p q w lam2).EW (fun b => (lam2 b : ℚ)) h

def RealGen : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Antitone lam2 → (∀ b, lam2 b ≤ w) →
    ∀ S : Submodule ℚ (rationalBlockModuleSetting p q w lam2).W, Stab (rationalBlockModuleSetting p q w lam2).EW S →
      (∀ v, IsHW (rationalBlockModuleSetting p q w lam2).EW (fun b => (lam2 b : ℚ)) v → v ∈ S) → S = ⊤

end Formalism.CohomologicalDescent.LPR
