import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem card_roots_map_pol (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (φ : G.F →+* ℂ) :
    ((P.pol.map φ).roots.toFinset).card = G.n ∧ P.pol.Monic := by
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hmon : P.pol.Monic := minpoly.monic hint
  refine ⟨?_, hmon⟩
  have hsep : (P.pol.map φ).Separable := P.reg.2.map
  have hdeg : (P.pol.map φ).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact P.reg.1
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), ← hdeg]
  exact IsAlgClosed.card_roots_eq_natDegree

end GlobalTheory.LKMid.Pair
