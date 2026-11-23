import Mathlib

universe u_1 u_2 u_3

namespace GlobalTheory.LatticeLinearEquivBasis

open Module

theorem span_range_basis_coe {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    {ι : Type*} (A : Submodule R V) (b : Basis ι R A) :
    Submodule.span R (Set.range fun i => (b i : V)) = A := by
  have h : Set.range (fun i => (b i : V)) = A.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_linearEquiv_map_lattice_eq : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R] (K : Type u_2) [inst_3 : Field K] [inst_4 : Algebra R K] [IsFractionRing R K] {V : Type u_3} [inst_6 : AddCommGroup V] [inst_7 : Module K V] [inst_8 : Module R V] [inst_9 : IsScalarTower R K V] (A B : Submodule R V) [Submodule.IsLattice K A] [Submodule.IsLattice K B], Exists fun (g : LinearEquiv (RingHom.id K) V V) ↦ Eq (Submodule.map (LinearMap.restrictScalars R (LinearEquiv.toLinearMap g)) A) B := by
  intro R _ _ _ K _ _ _ V _ _ _ _ A B _ _
  let bA := Free.chooseBasis R A
  let bB := Free.chooseBasis R B
  let eA := bA.extendOfIsLattice K
  let eB := bB.extendOfIsLattice K
  let e := eA.indexEquiv eB
  refine ⟨eA.equiv eB e, ?_⟩
  have hA := span_range_basis_coe A bA
  have hB := span_range_basis_coe B bB
  suffices h : Submodule.map ((eA.equiv eB e : V ≃ₗ[K] V).toLinearMap.restrictScalars R)
      (Submodule.span R (Set.range fun i => (bA i : V))) =
      Submodule.span R (Set.range fun j => (bB j : V)) by
    rw [hA, hB] at h; exact h
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨e i, ?_⟩
    have h1 : (bA i : V) = eA i := (bA.extendOfIsLattice_apply K i).symm
    have h2 : (bB (e i) : V) = eB (e i) := (bB.extendOfIsLattice_apply K (e i)).symm
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [h1, h2, Basis.equiv_apply]
  · rintro ⟨j, rfl⟩
    refine ⟨(bA (e.symm j) : V), ⟨e.symm j, rfl⟩, ?_⟩
    have h1 : (bA (e.symm j) : V) = eA (e.symm j) := (bA.extendOfIsLattice_apply K _).symm
    have h2 : (bB j : V) = eB j := (bB.extendOfIsLattice_apply K j).symm
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [h1, h2, Basis.equiv_apply, Equiv.apply_symm_apply]

end GlobalTheory.LatticeLinearEquivBasis
