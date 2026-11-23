import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsetOfClosedFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.ClosedSub

theorem closed_subset_support_proper {A : Type} [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (O : X.Opens) (C : Set X) (hC : IsClosed C)
    (hCO : C ⊆ (O : Set X)) :
    ∃ T' : (O : Scheme.{0}).IdealSheafData,
      (T'.support : Set (O : Scheme.{0})) = O.ι.base ⁻¹' C ∧
        IsProper (T'.subschemeι ≫ O.ι ≫ (X ↘ Spec (.of A))) := by
  have hC' : IsClosed (O.ι.base ⁻¹' C) := hC.preimage O.ι.continuous
  refine ⟨Scheme.IdealSheafData.vanishingIdeal ⟨_, hC'⟩, by simp, ?_⟩
  set T' := Scheme.IdealSheafData.vanishingIdeal (X := (O : Scheme.{0})) ⟨_, hC'⟩
  have hrange : Set.range (T'.subschemeι ≫ O.ι) = C := by
    have h : Set.range (T'.subschemeι ≫ O.ι) = O.ι '' Set.range T'.subschemeι := by
      rw [← Set.range_comp]
      rfl
    rw [h, Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change O.ι '' (O.ι ⁻¹' C) = C
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact Set.inter_eq_left.mpr hCO
  have : IsClosedImmersion (T'.subschemeι ≫ O.ι) :=
    IsClosedImmersion.of_isPreimmersion _ (hrange ▸ hC)
  rw [← Category.assoc]
  infer_instance

end GlobalTheory.CompanionTheory.GE.ClosedSub
