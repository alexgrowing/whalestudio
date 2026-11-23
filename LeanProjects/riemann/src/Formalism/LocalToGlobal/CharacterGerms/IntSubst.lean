import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

variable {C : Type} [Field C]

def IntS (V : VF C) {σ : Type} (F : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, V.Ge 0 (MvPowerSeries.coeff μ F)

def IntSubst (V : VF C) : Prop :=
  ∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ C),
    (∀ s, MvPowerSeries.constantCoeff (a s) = 0) → (∀ s, IntS V (a s)) →
    ∀ F : MvPowerSeries σ C, IntS V F → IntS V (MvPowerSeries.subst a F)

def TInt (V : VF C) : Prop :=
  ∀ (d : ℕ) (I₁ J₁ : Type) [Fintype I₁] [Fintype J₁] (X₁ : Cart V d I₁ J₁) (S : Sys X₁),
    (∀ c s x, V.Ge 0 (S.al c s x)) → ∀ t : I₁ → MvPowerSeries I₁ C, S.IsT t → ∀ c, IntS V (t c)

def TInv (V : VF C) : Prop :=
  ∀ (d : ℕ) (I₁ J₁ : Type) [Fintype I₁] [Fintype J₁] (X₁ : Cart V d I₁ J₁) (S : Sys X₁),
    (∀ c s x, V.Ge 0 (S.al c s x)) → ∀ t : I₁ → MvPowerSeries I₁ C, S.IsT t →
    ∃ Φ : I₁ → MvPowerSeries I₁ C, (∀ x, IntS V (Φ x)) ∧
      (∀ x, MvPowerSeries.constantCoeff (Φ x) = 0) ∧
      ∀ x, MvPowerSeries.subst t (Φ x) = (MvPowerSeries.X x : MvPowerSeries I₁ C)

def GermEq (V : VF C) : Prop :=
  ∀ (I : Fin 2 → Type) [∀ g, Fintype (I g)] (t Φ : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) → (∀ g c, IntS V (t g c)) →
    (∀ g x, MvPowerSeries.constantCoeff (Φ g x) = 0) → (∀ g x, IntS V (Φ g x)) →
    (∀ g x, MvPowerSeries.subst (t g) (Φ g x) = (MvPowerSeries.X x : MvPowerSeries (I g) C)) →
    IntGerm V t = {F | IntS V F}

end Formalism.L2.FormalSeriesBounds
