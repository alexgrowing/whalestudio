import Mathlib
open CategoryTheory AlgebraicGeometry
namespace GlobalTheory

theorem appLE_injective_of_genericPoint_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) (hπ : π (genericPoint Y) = genericPoint X) {U : X.Opens} {V : Y.Opens}
    (hV : (V : Set Y).Nonempty) (h : V ≤ π ⁻¹ᵁ U) :
    Function.Injective (π.appLE U V h).hom := by
  have hy : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hxU : π (genericPoint Y) ∈ U := h hy
  have hF : IsField (X.presheaf.stalk (π (genericPoint Y))) :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (by rw [hπ]; simp [irreducibleComponents_eq_singleton])
  letI := hF.toField
  have key : ∀ s, (π.stalkMap (genericPoint Y)).hom (X.presheaf.germ U _ hxU s) =
      Y.presheaf.germ V (genericPoint Y) hy ((π.appLE U V h).hom s) := by
    intro s
    rw [Scheme.Hom.germ_stalkMap_apply]
    simp [Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]
  intro s t hst
  apply germ_injective_of_isIntegral X _ hxU
  apply (π.stalkMap (genericPoint Y)).hom.injective
  rw [key, key, hst]

end GlobalTheory
