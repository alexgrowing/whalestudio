import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem grpObj_of_mono_factor {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A K : C} [GrpObj A] (i : K ⟶ A) [Mono i] (m : K ⊗ K ⟶ K) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[A])
    (e : 𝟙_ C ⟶ K) (he : e ≫ i = η[A]) (v : K ⟶ K) (hv : v ≫ i = i ≫ ι[A]) :
    ∃ _ : GrpObj K, IsMonHom i := by
  letI M : MonObj K :=
    { one := e, mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : e ▷ K ≫ (i ⊗ₘ i) = 𝟙_ C ◁ i ≫ η[A] ▷ A := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, he, tensorHom_def']
        rw [reassoc_of% h1, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : K ◁ e ≫ (i ⊗ₘ i) = i ▷ 𝟙_ C ≫ A ◁ η[A] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, he, MonoidalCategory.tensorHom_def]
        rw [reassoc_of% h1, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono i]
        have h1 : m ▷ K ≫ m ≫ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[A] ▷ A ≫ μ[A] := by
          simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        have h2 : K ◁ m ≫ m ≫ i = (i ⊗ₘ (i ⊗ₘ i)) ≫ A ◁ μ[A] ≫ μ[A] := by
          simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        simp only [Category.assoc]
        rw [h1, h2, MonObj.mul_assoc (X := A), associator_naturality_assoc] }
  letI G : GrpObj K :=
    { inv := v
      left_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift v (𝟙 K) ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift (i ≫ ι[A]) i = i ≫ lift ι[A] (𝟙 A) := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.left_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)]
      right_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift (𝟙 K) v ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift i (i ≫ ι[A]) = i ≫ lift (𝟙 A) ι[A] := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.right_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)] }
  exact ⟨G, { one_hom := he, mul_hom := hm }⟩

theorem overScheme_grpObj_of_mono_factor : ∀ (T : Scheme.{0}) (A K : Over T) [GrpObj A] (i : K ⟶ A),
    Mono i → (∃ m : K ⊗ K ⟶ K, m ≫ i = (i ⊗ₘ i) ≫ μ[A]) → (∃ e : 𝟙_ (Over T) ⟶ K, e ≫ i = η[A]) →
    (∃ v : K ⟶ K, v ≫ i = i ≫ ι[A]) → ∃ _ : GrpObj K, IsMonHom i := by
  intro T A K _ i hi ⟨m, hm⟩ ⟨e, he⟩ ⟨v, hv⟩
  exact grpObj_of_mono_factor i m hm e he v hv

end GlobalTheory
