import Mathlib

namespace GlobalTheory

theorem linearMap_continuous_of_compactSpace_of_finite
    {O : Type} [CommRing O] [TopologicalSpace O] [CompactSpace O] {M M' : Type}
    [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] [T2Space M] [Module.Finite O M] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousSMul O M']
    (f : M →ₗ[O] M') : Continuous f := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' O M
  have hgc : Continuous g := g.continuous_on_pi
  have hq : Topology.IsQuotientMap g := hgc.isClosedMap.isQuotientMap hgc hg
  have hfg : Continuous (f ∘ g) := (f.comp g).continuous_on_pi
  exact hq.continuous_iff.mpr hfg

end GlobalTheory
