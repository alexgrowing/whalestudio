import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CoeffEqZeroOfSumEqZero

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries Formalism.MainNotions.N.FrobeniusPowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def wdeg (g : O⟦X⟧) : ℕ := (g.map (IsLocalRing.residue O)).order.toNat

def IsDist (g : O⟦X⟧) : Prop := g.map (IsLocalRing.residue O) ≠ 0

theorem exists_weierstrass_substitution (g : O⟦X⟧) (hg : IsDist g) (hD : 1 ≤ wdeg g) :
    ∃ h : O⟦X⟧ →ₐ[O] O⟦X⟧, h X = g ∧ Function.Injective h ∧
      ∀ f : O⟦X⟧, ∃! c : Fin (wdeg g) → O⟦X⟧, f = ∑ i : Fin (wdeg g), X ^ (i : ℕ) * h (c i) := by
  have hg0 : constantCoeff g ∈ IsLocalRing.maximalIdeal O := WeierD.constantCoeff_mem (g := g) hD
  obtain ⟨h, hX⟩ := WeierS.exists_algHom_X_eq hg0
  refine ⟨h, hX, WeierD.injective (g := g) hg hD h hX, fun f => ?_⟩
  obtain ⟨c, hc⟩ := WeierD.exists_decomp (g := g) hg hD h hX f
  exact ⟨c, hc, fun c' hc' => WeierD.decomp_unique (g := g) hg h hX c' c (hc'.symm.trans hc)⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
