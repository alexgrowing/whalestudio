import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteImageOfLocallyConstantOnHolomorphicFamilie
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.OpenSubgroupPts

open GlobalTheory.Points

theorem isPreconnected_affineOpen {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p]
    {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsPreconnected {x : Pts p | ⊤ ≤ x.1 ⁻¹ᵁ U} := by
  have key : ∀ {R : CommRingCat.{0}} [IsDomain R] (q : Spec R ⟶ Sp ℂ) [LocallyOfFiniteType q],
      PreconnectedSpace (Pts q) := by
    intro R _ q hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact FiniteClasses.preconnectedSpace_pts R
  have := key (hU.fromSpec ≫ p)
  have h := isPreconnected_range (PtsOver.continuous_map (C := ℂ) hU.fromSpec (q := p) rfl (𝟙 _))
  rw [PtsOver.range_map, range_comp_of_isOpenImmersion, hU.opensRange_fromSpec] at h
  exact h

theorem preconnectedSpace_pts_of_isIntegral {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ)
    [LocallyOfFiniteType p] : PreconnectedSpace (Pts p) := by
  refine ⟨isPreconnected_of_forall_pair fun x _ y _ => ?_⟩
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_le x.1 (le_preimage_top _)
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top _)
  have hx' := (le_preimage_iff x.1 U).1 hx
  have hy' := (le_preimage_iff y.1 V).1 hy
  have : Nonempty U := ⟨⟨_, hx'⟩⟩
  have : Nonempty V := ⟨⟨_, hy'⟩⟩
  obtain ⟨z, hz, hzm⟩ := ComplexPoints.exists_point_mem p (Z := (U : Set Y) ∩ V)
    (U.isOpen.inter V.isOpen).isLocallyClosed
    (nonempty_preirreducible_inter U.isOpen V.isOpen ⟨_, hx'⟩ ⟨_, hy'⟩)
  exact ⟨_, Set.subset_univ _, Or.inl hx, Or.inr hy, IsPreconnected.union (⟨z, hz⟩ : Pts p)
    ((le_preimage_iff z U).2 (hzm _).1) ((le_preimage_iff z V).2 (hzm _).2)
    (isPreconnected_affineOpen p hU) (isPreconnected_affineOpen p hV)⟩

theorem subgroup_eq_top_of_nhds_one :
    ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp ℂ ⟶ X) (H : Subgroup (Over.mk x ⟶ G)) (U : G.left.Opens) (κ : Type) [Fintype κ] (f : κ → Γ(G.left, U)) (O : Set (κ → ℂ)), Smooth G.hom → GeometricallyConnected G.hom → IsOpen O → ⊤ ≤ (show Sp ℂ ⟶ G.left from (1 : Over.mk x ⟶ G).left) ⁻¹ᵁ U → (fun j => valAt' (1 : Over.mk x ⟶ G).left U (f j)) ∈ O → (∀ a : Over.mk x ⟶ G, ⊤ ≤ (show Sp ℂ ⟶ G.left from a.left) ⁻¹ᵁ U → (fun j => valAt' a.left U (f j)) ∈ O → a ∈ H) → H = ⊤ := by
  intro X G _ x H U κ _ f O hs hc hO h1 h1O hH
  let p := pullback.snd G.hom x
  have : IsIntegral (pullback G.hom x) :=
    isIntegral_of_isPullback_of_smooth (IsPullback.of_hasPullback G.hom x)
  have := preconnectedSpace_pts_of_isIntegral p
  let Y : Over X := Over.mk (p ≫ x)
  let π : Y ⟶ G := Over.homMk (pullback.fst G.hom x) pullback.condition
  let s : Y ⟶ Over.mk x := Over.homMk p rfl
  let inc : Pts p → (Over.mk x ⟶ Y) := fun y => Over.homMk y.1 (by
    show y.1 ≫ p ≫ x = x
    rw [← Category.assoc, y.2, Category.id_comp])
  have hin : ∀ y, inc y ≫ s = 𝟙 _ := fun y => Over.OverMorphism.ext y.2
  have hsurj : ∀ a : Over.mk x ⟶ G, ∃ y, inc y ≫ π = a := fun a =>
    ⟨⟨pullback.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp x).symm), pullback.lift_snd _ _ _⟩,
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hopen : IsOpen {z : Sp ℂ ⟶ G.left | ⊤ ≤ z ⁻¹ᵁ U ∧ (fun j => valAt' z U (f j)) ∈ O} :=
    (continuousOn_pi.2 fun j => continuousOn_valR (C := ℂ) (f j)).isOpen_inter_preimage
      (isOpen_setOf_le_preimage U) hO
  have hl : IsLocallyConstant fun y : Pts p => inc y ≫ π ∈ H := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    let τ : Y ⟶ G := (s ≫ (inc y₀ ≫ π)⁻¹) * π
    have hτ : ∀ y, inc y ≫ τ = (inc y₀ ≫ π)⁻¹ * (inc y ≫ π) := fun y => by
      rw [MonObj.comp_mul, ← Category.assoc, hin, Category.id_comp]
    have hcont : Continuous fun y : Pts p => (show Sp ℂ ⟶ G.left from (inc y ≫ τ).left) :=
      (continuous_comp (C := ℂ) (X := pullback G.hom x) τ.left).comp continuous_subtype_val
    have hN := (hopen.preimage hcont).mem_nhds (x := y₀) (by
      simp only [Set.mem_preimage, hτ, inv_mul_cancel]
      exact ⟨h1, h1O⟩)
    filter_upwards [hN] with y hy
    have h := hH _ hy.1 hy.2
    rw [hτ] at h
    have h' := H.mul_mem_cancel_right (y := inc y₀ ≫ π) h
    rw [mul_inv_cancel_left] at h'
    exact propext h'
  rw [eq_top_iff]
  intro a _
  obtain ⟨y, rfl⟩ := hsurj a
  obtain ⟨y₁, hy₁⟩ := hsurj 1
  have h := hl.apply_eq_of_preconnectedSpace y y₁
  simp only [hy₁] at h
  rw [h]
  exact H.one_mem

end GlobalTheory.OpenSubgroupPts
