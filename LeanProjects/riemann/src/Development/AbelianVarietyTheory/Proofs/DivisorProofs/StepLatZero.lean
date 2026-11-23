import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.Mean4O GlobalTheory.LieHt

namespace GlobalTheory.LieRead

variable {D : D7} (O : Setup D)

def FibTie (y : Pt O.s) {K : Type} [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) : Prop :=
  ∃ (jF : O.κ.c.F →+* K) (yO : Sp (𝓞 K) ⟶ O.s.T.Z.X) (ψ : F.G.left ⟶ O.s.T.Z.t.G.left),
    ι.comp jF = y.fK ∧
    spMap (ι.comp (algebraMap (𝓞 K) K)) ≫ yO = y.y ≫ genι O.s.T.Z ∧
    IsGrpPullback F.G O.s.T.Z.t.G yO ψ ∧
    LBIso (O.s.T.Z.t.PP.L.pull (F.φ ≫ ψ)) F.P₀.L ∧
    F.P₀.g = (letters O.S.Dw).length ∧
    ∀ (k : Fin F.P₀.g) (x : Letter O.S.Dw), (letters O.S.Dw)[(k : ℕ)]? = some x →
      y.u x.1 x.2 = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ (F.v k).left ≫ F.φ ≫ ψ

def stepLat {K : Type} [Field K] [NumberField K] (F : SemiFib K) (τ : D.host.E →+* ℂ) (k : ℕ) :
    Submodule (𝓞 K) (Fin F.P₀.g → K) :=
  F.lieLat ⊓ (Submodule.span K {v | ∃ (i : Fin F.P₀.g) (x : Letter O.S.Dw), x.1 = τ ∧ (x.2 : ℕ) < k ∧
    (letters O.S.Dw)[(i : ℕ)]? = some x ∧ v = Pi.single i 1}).restrictScalars (𝓞 K)

theorem stepLat_zero {K : Type} [Field K] [NumberField K] (F : SemiFib K) (τ : D.host.E →+* ℂ) :
    stepLat O F τ 0 = ⊥ := by
  have : {v : Fin F.P₀.g → K | ∃ (i : Fin F.P₀.g) (x : Letter O.S.Dw), x.1 = τ ∧ (x.2 : ℕ) < 0 ∧
      (letters O.S.Dw)[(i : ℕ)]? = some x ∧ v = Pi.single i 1} = ∅ := by
    ext v; simp
  rw [stepLat, this, Submodule.span_empty, Submodule.restrictScalars_bot, inf_bot_eq]

end GlobalTheory.LieRead

end
