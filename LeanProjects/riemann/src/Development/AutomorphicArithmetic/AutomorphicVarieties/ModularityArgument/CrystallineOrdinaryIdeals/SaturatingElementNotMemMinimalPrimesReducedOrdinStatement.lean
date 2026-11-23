import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementNotMemMinimalPrimesReducedOrdin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturatingElement_notMem_minimalPrimes_reducedOrdinaryIdeal : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) (U : D.Univ), ∀ P ∈ (GlobalTheory.OrdLoc.Icr D U).minimalPrimes, GlobalTheory.OrdLoc.del D U.r.hom ∉ P := by
  intro l _ O _ _ _ D U P hP hdel
  have hmem : ∀ a, a ∈ D.IY U ↔ ∃ n, D.del U.r.hom ^ n * a ∈ D.ordIdeal U.r.hom := by
    intro a
    rw [UpperTheory.V.Loc.Dat3.IY.eq_1]
    rfl
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hdel
  apply hy
  rw [UpperTheory.V.Loc.Dat3.Icr.eq_1] at hxy ⊢
  obtain ⟨k, hk⟩ := hxy
  obtain ⟨n, hn⟩ := (hmem _).1 hk
  refine ⟨k, (hmem _).2 ⟨n + k, ?_⟩⟩
  have e : D.del U.r.hom ^ (n + k) * y ^ k = D.del U.r.hom ^ n * (D.del U.r.hom * y) ^ k := by
    ring
  rw [e]
  exact hn
