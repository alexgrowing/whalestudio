import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem cup_compare_degree_zero_two {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {R : Type}
    [CommRing R] {M M' P : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [AddCommGroup M'] [Module R M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M'] [AddCommGroup P]
    [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (rho : Representation R G M) (rho' : Representation R G M') (rhoP : Representation R G P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V) (eC : P ≃+ C.V)
    (heB : ∀ g m, eB (rho' g m) = B.ρ g (eB m))
    (μ : A ⊗ B ⟶ C) (hbμ : ∀ x y, eC (b x y) = μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y))
    (m : H0 rho) (z' : Z2 rho') (x : cocycles A 0) (x' : cocycles B 2)
    (hx : ∀ s, cochainOf A (cocycleι A 0 x) s = eA m.1)
    (hx' : ∀ s, cochainOf B (cocycleι B 2 x') s = eB (z'.1 (s 0, s 1))) :
    ∃ y : cocycles C 2,
      (∀ s, cochainOf C (cocycleι C 2 y) s = eC ((cupCocycleH0Z2 rho rho' rhoP b hb hbe m z').1 (s 0, s 1))) ∧
      cohomologyπ C 2 y = cupPairing μ (rfl : 0 + 2 = 2)
        (cohomologyπ A 0 x) (cohomologyπ B 2 x') := by
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cupCocycles (rfl : 0 + 2 = 2) x x'),
    fun s => ?_, (cupPairing_cohomologyπ μ rfl x x').symm⟩
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx', cupCocycleH0Z2_apply, hbμ]
  have h0 : Fin.partialProd s ⟨0, by omega⟩ = 1 := Fin.partialProd_zero s
  rw [h0, map_one]
  rfl

theorem cup_compare_degree_two_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {R : Type}
    [CommRing R] {M M' P : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [AddCommGroup M'] [Module R M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M'] [AddCommGroup P]
    [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (rho : Representation R G M) (rho' : Representation R G M') (rhoP : Representation R G P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V) (eC : P ≃+ C.V)
    (heB : ∀ g m, eB (rho' g m) = B.ρ g (eB m))
    (μ : A ⊗ B ⟶ C) (hbμ : ∀ x y, eC (b x y) = μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y))
    (z : Z2 rho) (m : H0 rho') (x : cocycles A 2) (x' : cocycles B 0)
    (hx : ∀ s, cochainOf A (cocycleι A 2 x) s = eA (z.1 (s 0, s 1)))
    (hx' : ∀ s, cochainOf B (cocycleι B 0 x') s = eB m.1) :
    ∃ y : cocycles C 2,
      (∀ s, cochainOf C (cocycleι C 2 y) s = eC ((cupCocycleZ2H0 rho rho' rhoP b hb hbe z m).1 (s 0, s 1))) ∧
      cohomologyπ C 2 y = cupPairing μ (rfl : 2 + 0 = 2)
        (cohomologyπ A 2 x) (cohomologyπ B 0 x') := by
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cupCocycles (rfl : 2 + 0 = 2) x x'),
    fun s => ?_, (cupPairing_cohomologyπ μ rfl x x').symm⟩
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx', cupCocycleZ2H0_apply, hbμ, ← heB,
    (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2]

end PositivityTheory.Lit1.PTN
