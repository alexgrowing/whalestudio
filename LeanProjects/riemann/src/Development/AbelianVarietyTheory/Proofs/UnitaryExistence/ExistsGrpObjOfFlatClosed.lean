import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

theorem exists_grpObj_of_mono {H G : C} [GrpObj G] (j : H ⟶ G) [Mono j]
    (o : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (n : H ⟶ H) (ho : o ≫ j = η[G])
    (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[G]) (hn : n ≫ j = j ≫ GrpObj.inv) :
    ∃ _ : GrpObj H, IsMonHom j := by
  letI M : MonObj H :=
    { one := o
      mul := m
      one_mul := by
        rw [← cancel_mono j, Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono j, Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono j]
        simp only [Category.assoc, hm]
        rw [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          tensorHom_comp_tensorHom_assoc, hm, Category.id_comp]
        have h1 : ((j ⊗ₘ j) ≫ μ[G] ⊗ₘ j) = ((j ⊗ₘ j) ⊗ₘ j) ≫ μ[G] ▷ G := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
        have h2 : (j ⊗ₘ (j ⊗ₘ j) ≫ μ[G]) = (j ⊗ₘ (j ⊗ₘ j)) ≫ G ◁ μ[G] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
        rw [h1, h2, Category.assoc, Category.assoc, MonObj.mul_assoc, associator_naturality_assoc] }
  refine ⟨{ inv := n, left_inv := ?_, right_inv := ?_ }, ⟨ho, hm⟩⟩
  · rw [← cancel_mono j]
    change (lift n (𝟙 H) ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.left_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this
  · rw [← cancel_mono j]
    change (lift (𝟙 H) n ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.right_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this

theorem isMonHom_of_comp_mono {A B D : C} [MonObj A] [MonObj B] [MonObj D] (e : A ⟶ B) (i : B ⟶ D)
    [Mono i] [IsMonHom i] [h : IsMonHom (e ≫ i)] : IsMonHom e := by
  constructor
  · rw [← cancel_mono i, Category.assoc, h.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, h.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

theorem isCommMonObj_of_mono [BraidedCategory C] {H G : C} [MonObj H] [MonObj G] (j : H ⟶ G)
    [Mono j] [IsMonHom j] [IsCommMonObj G] : IsCommMonObj H := by
  constructor
  rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

end

theorem exists_grpObj_of_flat_closed {S S' : Scheme.{0}} (f : S' ⟶ S)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (P Ga : Over S) [GrpObj P] (io : Ga ⟶ P)
    (Z : Over S') [GrpObj Z] (i : Z ⟶ (Over.pullback f).obj P) (e : (Over.pullback f).obj Ga ≅ Z)
    [IsClosedImmersion io.left] [Flat Ga.hom] [hi : IsMonHom i]
    (h : e.hom ≫ i = (Over.pullback f).map io) :
    ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  have h1 : Flat (𝟙_ (Over S)).hom := inferInstanceAs (Flat (𝟙 S))
  have h2 : Flat (Ga ⊗ Ga).hom := inferInstanceAs (Flat (pullback.fst Ga.hom Ga.hom ≫ Ga.hom))
  have hm : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hm' : Mono ((Over.pullback f).map io) := inferInstance
  have h' : e.inv ≫ (Over.pullback f).map io = i := by rw [← h, e.inv_hom_id_assoc]
  have hmi : Mono i := by rw [← h']; infer_instance
  obtain ⟨o, ⟨ho, -⟩, -⟩ := existsUnique_lift_of_flat f io η[P]
    (Functor.OplaxMonoidal.η (Over.pullback f) ≫ η[Z] ≫ e.inv) (by
      rw [Category.assoc, Category.assoc, h', hi.one_hom, Functor.obj.η_def,
        Functor.Monoidal.η_ε_assoc])
  obtain ⟨m, ⟨hm, -⟩, -⟩ := existsUnique_lift_of_flat f io ((io ⊗ₘ io) ≫ μ[P])
    (Functor.OplaxMonoidal.δ (Over.pullback f) Ga Ga ≫ (e.hom ⊗ₘ e.hom) ≫ μ[Z] ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', hi.mul_hom, tensorHom_comp_tensorHom_assoc, h, Functor.obj.μ_def,
        Functor.LaxMonoidal.μ_natural_assoc, Functor.Monoidal.δ_μ_assoc, Functor.map_comp])
  obtain ⟨n, ⟨hn, -⟩, -⟩ := existsUnique_lift_of_flat f io (io ≫ GrpObj.inv)
    (e.hom ≫ GrpObj.inv ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', GrpObj.inv_hom, ← Category.assoc, h, Functor.obj.ι_def, Functor.map_comp])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono io o m n ho hm hn
  refine ⟨G, hG, ?_, fun _ => isCommMonObj_of_mono io⟩
  have : IsMonHom (e.hom ≫ i) := by rw [h]; infer_instance
  exact isMonHom_of_comp_mono e.hom i

theorem flat_closure_subgroup :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (P Ga : Over (Sp T)) [GrpObj P] (io : Ga ⟶ P) (Z : Over (Sp K)) [GrpObj Z] (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj P) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left → Flat Ga.hom → IsMonHom i → e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io → ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  intro T K _ _ _ _ _ _ P Ga _ io Z _ i e _ _ _ h
  have := schemeTheoreticallyDominant_fractionField T K
  exact exists_grpObj_of_flat_closed _ P Ga io Z i e h

end GlobalTheory
