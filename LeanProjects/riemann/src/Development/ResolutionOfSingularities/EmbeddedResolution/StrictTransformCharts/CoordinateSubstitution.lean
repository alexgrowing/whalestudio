import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem coordSubspaceIdeal_empty (k : Type u) [Field k] (m : ℕ) :
    coordSubspaceIdeal k m (∅ : Finset (Fin m)) = ⊥ := by
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  simp only [Finset.coe_empty, Set.image_empty, Ideal.span_empty]
  ext U
  simp [Ideal.map_bot]

theorem coordSubspaceIdeal_singleton (k : Type u) [Field k] (m : ℕ) (j : Fin m) :
    coordSubspaceIdeal k m {j} =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)}) := by
  have h : ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
      (({j} : Finset (Fin m)) : Set (Fin m))) =
      {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)} := by
    rw [Finset.coe_singleton, Set.image_singleton]
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, h]

def coordBlowupSubstMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    affineSpaceFin k m ⟶ affineSpaceFin k m :=
  AffineSpace.homOfVector (affineSpaceFinToSpec k m)
    (fun i : ULift.{u} (Fin m) =>
      if i.down ∈ S ∧ i.down ≠ s then
        AffineSpace.coord (Spec (CommRingCat.of k)) i *
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)
      else AffineSpace.coord (Spec (CommRingCat.of k)) i)

@[simp]
theorem coordBlowupSubstMap_comp_affineSpaceFinToSpec (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m = affineSpaceFinToSpec k m := by
  apply AffineSpace.homOfVector_over

@[simp]
theorem coordBlowupSubstMap_appTop_coord (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (i : ULift.{u} (Fin m)) :
    (coordBlowupSubstMap k m S s).appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      if i.down ∈ S ∧ i.down ≠ s then
        AffineSpace.coord (Spec (CommRingCat.of k)) i *
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)
      else AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  exact AffineSpace.homOfVector_appTop_coord ..

theorem coordBlowupSubstMap_appTop_coord_of_mem (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j) *
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by
  have hc : (ULift.up j : ULift.{u} (Fin m)).down ∈ S ∧
      (ULift.up j : ULift.{u} (Fin m)).down ≠ s := ⟨hj, hjs⟩
  rw [coordBlowupSubstMap_appTop_coord k m S s (ULift.up j : ULift.{u} (Fin m)), if_pos hc]

theorem coordBlowupSubstMap_appTop_coord_self (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by
  have hc : ¬ ((ULift.up s : ULift.{u} (Fin m)).down ∈ S ∧
      (ULift.up s : ULift.{u} (Fin m)).down ≠ s) := by
    rintro ⟨-, h⟩
    exact h rfl
  rw [coordBlowupSubstMap_appTop_coord k m S s (ULift.up s : ULift.{u} (Fin m)), if_neg hc]

theorem coordBlowupSubstMap_appTop_coord_of_notMem (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) (j : Fin m) (hj : j ∉ S) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j) := by
  have hc : ¬ ((ULift.up j : ULift.{u} (Fin m)).down ∈ S ∧
      (ULift.up j : ULift.{u} (Fin m)).down ≠ s) := fun h => hj h.1
  rw [coordBlowupSubstMap_appTop_coord k m S s (ULift.up j : ULift.{u} (Fin m)), if_neg hc]

theorem comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_mem (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s) :
    (coordSubspaceIdeal k m {j}).comap (coordBlowupSubstMap k m S s) =
      coordSubspaceIdeal k m {j} * coordSubspaceIdeal k m {s} := by
  rw [coordSubspaceIdeal_singleton, coordSubspaceIdeal_singleton,
    Scheme.IdealSheafData.comap_ofIdealTop,
    ← Scheme.IdealSheafData.ofIdealTop_mul, Ideal.map_span, Set.image_singleton,
    coordBlowupSubstMap_appTop_coord_of_mem k m S s j hj hjs,
    Ideal.span_singleton_mul_span_singleton]

theorem comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) :
    (coordSubspaceIdeal k m {s}).comap (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {s} := by
  rw [coordSubspaceIdeal_singleton, Scheme.IdealSheafData.comap_ofIdealTop,
    Ideal.map_span, Set.image_singleton, coordBlowupSubstMap_appTop_coord_self k m S s]

theorem comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_notMem (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) (j : Fin m) (hj : j ∉ S) :
    (coordSubspaceIdeal k m {j}).comap (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {j} := by
  rw [coordSubspaceIdeal_singleton, Scheme.IdealSheafData.comap_ofIdealTop,
    Ideal.map_span, Set.image_singleton, coordBlowupSubstMap_appTop_coord_of_notMem k m S s j hj]

theorem comap_coordBlowupSubstMap_coordSubspaceIdeal_center (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    (coordSubspaceIdeal k m S).comap (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {s} := by
  have key : Ideal.map ((coordBlowupSubstMap k m S s).appTop.hom)
      (Ideal.span
        ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
          (S : Set (Fin m)))) =
      Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)} := by
    rw [Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro y ⟨z, ⟨i, hi, rfl⟩, rfl⟩
      have hiS : i ∈ S := Finset.mem_coe.mp hi
      show (coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ∈
          Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)}
      by_cases h : i = s
      · have h2 : (coordBlowupSubstMap k m S s).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) =
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by
          rw [h]
          exact coordBlowupSubstMap_appTop_coord_self k m S s
        rw [h2]
        exact Ideal.mem_span_singleton_self _
      · rw [coordBlowupSubstMap_appTop_coord_of_mem k m S s i hiS h]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hmem : (coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)) ∈
          ((coordBlowupSubstMap k m S s).appTop.hom ''
            ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
              (S : Set (Fin m)))) :=
        Set.mem_image_of_mem _ (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hs))
      rw [coordBlowupSubstMap_appTop_coord_self k m S s] at hmem
      exact Ideal.subset_span hmem
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, Scheme.IdealSheafData.comap_ofIdealTop, key,
    coordSubspaceIdeal_singleton]

theorem comap_coordIdeal_of_coordBlowupSubstMap {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {p₁ : X₁ ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : X₁.Opens} {m : ℕ} {S : Finset (Fin m)} {s : Fin m}
    (c : EtaleChart p U m) (c₁ : EtaleChart p₁ V m)
    (g : V.toScheme ⟶ U.toScheme)
    (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map) (T : Finset (Fin m)) :
    (c.coordIdeal T).comap g =
      ((coordSubspaceIdeal k m T).comap (coordBlowupSubstMap k m S s)).comap c₁.map := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, ← Scheme.IdealSheafData.comap_comp, ← hg,
    Scheme.IdealSheafData.comap_comp]

theorem comap_coordIdeal_singleton_of_mem {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {p₁ : X₁ ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : X₁.Opens} {m : ℕ} {S : Finset (Fin m)} {s : Fin m}
    (c : EtaleChart p U m) (c₁ : EtaleChart p₁ V m)
    (g : V.toScheme ⟶ U.toScheme)
    (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map)
    (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s) :
    (c.coordIdeal {j}).comap g = c₁.coordIdeal {j} * c₁.coordIdeal {s} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg {j},
    comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_mem k m S s j hj hjs,
    Scheme.IdealSheafData.comap_mul]
  rfl

theorem comap_coordIdeal_singleton_self {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {p₁ : X₁ ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : X₁.Opens} {m : ℕ} {S : Finset (Fin m)} {s : Fin m}
    (c : EtaleChart p U m) (c₁ : EtaleChart p₁ V m)
    (g : V.toScheme ⟶ U.toScheme)
    (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map) :
    (c.coordIdeal {s}).comap g = c₁.coordIdeal {s} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg {s},
    comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self k m S s]
  rfl

theorem comap_coordIdeal_singleton_of_notMem {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {p₁ : X₁ ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : X₁.Opens} {m : ℕ} {S : Finset (Fin m)} {s : Fin m}
    (c : EtaleChart p U m) (c₁ : EtaleChart p₁ V m)
    (g : V.toScheme ⟶ U.toScheme)
    (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map)
    (j : Fin m) (hj : j ∉ S) :
    (c.coordIdeal {j}).comap g = c₁.coordIdeal {j} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg {j},
    comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_notMem k m S s j hj]
  rfl

theorem comap_coordIdeal_center {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {p₁ : X₁ ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : X₁.Opens} {m : ℕ} {S : Finset (Fin m)} {s : Fin m}
    (c : EtaleChart p U m) (c₁ : EtaleChart p₁ V m)
    (g : V.toScheme ⟶ U.toScheme)
    (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map) (hs : s ∈ S) :
    (c.coordIdeal S).comap g = c₁.coordIdeal {s} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg S,
    comap_coordBlowupSubstMap_coordSubspaceIdeal_center k m S s hs]
  rfl

end FunctorialResolution.EmbeddedResolution

end
