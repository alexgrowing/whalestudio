import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ZariskiSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits IsLocalRing MonoidalCategory

universe u

noncomputable section

attribute [local instance] algebraOfOver

instance flat_fromSpecStalk (Y : Scheme.{u}) (y : Y) : Flat (Y.fromSpecStalk y) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  replace hV : IsAffineOpen V := hV
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hyV]
  change Flat (Spec.map (Y.presheaf.germ V y hyV) ≫ hV.fromSpec)
  have : Flat (Spec.map (Y.presheaf.germ V y hyV)) := by
    let _ : Algebra Γ(Y, V) (Y.presheaf.stalk y) := (Y.presheaf.germ V y hyV).hom.toAlgebra
    have := hV.isLocalization_stalk ⟨y, hyV⟩
    exact Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2
      (IsLocalization.flat (Y.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl))
  infer_instance

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)

end

end GroundTheory.Arith.SchemeCoh
