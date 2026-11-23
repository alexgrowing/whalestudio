import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem exists_finite_flat_spec_of_quasiFinite_of_henselian :
    ∀ (S : Type) [CommRing S] [HenselianLocalRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of S))
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f],
      (∃ y : Y, f y = IsLocalRing.closedPoint S) → ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A),
        Module.Finite S A ∧ Module.Flat S A ∧ Nontrivial A ∧
          ∃ h : Spec (.of A) ⟶ Y, h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S A)) := by
  intro S _ _ Y f _ _ _ _ _ ⟨y, hy⟩
  let F := finitePart f
  have hyF : y ∈ F := mem_finitePart_of_eq_closedPoint f y hy
  have hfin : IsFinite (F.ι ≫ f) := isFinite_finitePart f
  have : IsAffine F.toScheme := isAffine_of_isAffineHom (F.ι ≫ f)
  let g : Spec Γ(F.toScheme, ⊤) ⟶ Spec (.of S) := F.toScheme.isoSpec.inv ≫ F.ι ≫ f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  letI : Algebra S Γ(F.toScheme, ⊤) := φ.hom.toAlgebra
  have hφ' : CommRingCat.ofHom (algebraMap S Γ(F.toScheme, ⊤)) = φ := rfl
  have hgfin : IsFinite g := by dsimp [g]; infer_instance
  have hgfl : Flat g := by dsimp [g]; infer_instance
  refine ⟨Γ(F.toScheme, ⊤), inferInstance, inferInstance, ?_, ?_, ?_, F.toScheme.isoSpec.inv ≫ F.ι, ?_⟩
  · rw [← hφ, IsFinite.SpecMap_iff] at hgfin
    exact RingHom.finite_algebraMap.1 hgfin
  · rw [← hφ, Flat.SpecMap_iff] at hgfl
    exact RingHom.flat_algebraMap_iff.1 hgfl
  · have : Nonempty F.toScheme := ⟨⟨y, hyF⟩⟩
    let x : Spec Γ(F.toScheme, ⊤) := F.toScheme.isoSpec.hom ⟨y, hyF⟩
    have hp : x.asIdeal.IsPrime := x.isPrime
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hp.ne_top (Subsingleton.elim _ _)
  · rw [hφ', hφ]
    simp [g]

end GlobalTheory
