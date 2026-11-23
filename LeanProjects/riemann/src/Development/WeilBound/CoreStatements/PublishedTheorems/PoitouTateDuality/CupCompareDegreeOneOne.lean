import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem cup_compare_degree_one_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {R : Type}
    [CommRing R] {M M' P : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [AddCommGroup M'] [Module R M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M'] [AddCommGroup P]
    [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (rho : Representation R G M) (rho' : Representation R G M') (rhoP : Representation R G P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V) (eC : P ≃+ C.V)
    (heB : ∀ g m, eB (rho' g m) = B.ρ g (eB m))
    (μ : A ⊗ B ⟶ C) (hbμ : ∀ x y, eC (b x y) = μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y))
    (z : Z1 rho) (z' : Z1 rho') (x : cocycles A 1) (x' : cocycles B 1)
    (hx : ∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (s 0)))
    (hx' : ∀ s, cochainOf B (cocycleι B 1 x') s = eB (z'.1 (s 0))) :
    ∃ y : cocycles C 2,
      (∀ s, cochainOf C (cocycleι C 2 y) s = eC ((cupCocycleZ1Z1 rho rho' rhoP b hb hbe hc z z').1 (s 0, s 1))) ∧
      cohomologyπ C 2 y = cupPairing μ (rfl : 1 + 1 = 2)
        (cohomologyπ A 1 x) (cohomologyπ B 1 x') := by
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cupCocycles (rfl : 1 + 1 = 2) x x'),
    fun s => ?_, (cupPairing_cohomologyπ μ rfl x x').symm⟩
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx', cupCocycleZ1Z1_apply, hbμ, heB]
  have h1 : Fin.partialProd s ⟨1, by omega⟩ = s 0 := by
    show Fin.partialProd s (Fin.succ 0) = s 0
    rw [Fin.partialProd_succ]
    show Fin.partialProd s 0 * s 0 = s 0
    rw [Fin.partialProd_zero, one_mul]
  rw [h1]
  rfl

end PositivityTheory.Lit1.PTN
