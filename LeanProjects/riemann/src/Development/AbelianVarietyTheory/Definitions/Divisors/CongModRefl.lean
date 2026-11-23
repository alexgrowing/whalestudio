import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq

noncomputable section

namespace GlobalTheory.LevPull

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IntAt (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) : Prop := ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f

def Pull (d : DeltaDat Xo c 0) (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → evR d.Xo₂ d.c₂ g y₂ = evR Xo c f y

def FibConst (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → FrOver d y₂' y →
      evR d.Xo₂ d.c₂ g y₂ = evR d.Xo₂ d.c₂ g y₂'

theorem Pull.fibConst {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g) : FibConst d g :=
  fun k _ _ _ _ hk y₂ y₂' y h₁ h₂ => (h k hk y₂ y h₁).trans (h k hk y₂' y h₂).symm

variable (Dw l) in

abbrev LaQ : Type := Dw.La ⧸ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)

variable (Dw l) in

abbrev Gam : Type := LaQ Dw l ≃ₗ[𝓞 E] LaQ Dw l

def IsLift (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ γ, (Submodule.mkQ _) ∘ₗ lift γ = γ.toLinearMap ∘ₗ Submodule.mkQ _

def CongMod (I : Ideal (𝓞 E)) (h h' : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ a, h a - h' a ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La)

end GlobalTheory.LevPull
