import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame

open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

def PairUnitLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (p : Ideal (𝓞 K)), p.IsMaximal →
    ∀ (V : Type) [AddCommGroup V] [Module K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ w y : V, h y w = 1 → h w w ∈ locRing p → h y y ∈ locRing p →
      ∃ c ∈ locRing p, ∃ d ∈ locRing p, IsUnitIn (locRing p) (h (c • w + d • y) (c • w + d • y))

end PI.UnitaryGroupMassFormula.CntFormula.UG
