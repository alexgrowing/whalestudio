import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem mem_IY_of_del_mul_mem {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] (D : Dat3 l O) (U : D.Univ) {a : U.R}
    (h : del D U.r.hom * a ∈ IY D U) : a ∈ IY D U := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [pow_succ, mul_assoc]; exact hn⟩

theorem del_notMem_of_mem_minimalPrimes_Icr : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] (D : Dat3 l O) (U : D.Univ), ∀ P ∈ (GlobalTheory.OrdLoc.Icr D U).minimalPrimes,
    GlobalTheory.OrdLoc.del D U.r.hom ∉ P := by
  intro l _ O _ _ _ D U P hP hd
  rw [Icr, Ideal.radical_minimalPrimes] at hP
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hd
  exact hy (mem_IY_of_del_mul_mem D U hxy)

end GlobalTheory.OrdLoc

example : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) (U : D.Univ), ∀ P ∈ (GlobalTheory.OrdLoc.Icr D U).minimalPrimes, GlobalTheory.OrdLoc.del D U.r.hom ∉ P := GlobalTheory.OrdLoc.del_notMem_of_mem_minimalPrimes_Icr
