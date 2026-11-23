import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.BiprodPush

variable {R : Type} [CommRing R]

theorem cpush_comp (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f ≫ g) n x = cpush K g n (cpush K f n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  congr 1

theorem cpush_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f + g) n x = cpush K f n x + cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  rw [← CohomologyClass.mk_add]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_add, Cochain.comp_add]

theorem cpush_zero (K : Cx R) {I J : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  rw [← CohomologyClass.mk_zero]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_zero]

theorem cpush_id (K : Cx R) {I : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (𝟙 I) n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  congr 1
  ext1
  simp [zcomp]

def cpushHom (K : Cx R) (I J : Cx R) (n : ℤ) (x : CohomologyClass K I n) : (I ⟶ J) →+ CohomologyClass K J n where
  toFun f := cpush K f n x
  map_zero' := cpush_zero K n x
  map_add' f g := cpush_add K f g n x

theorem cpush_sum (K : Cx R) {I J : Cx R} {ι : Type} (s : Finset ι) (f : ι → (I ⟶ J)) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (∑ j ∈ s, f j) n x = ∑ j ∈ s, cpush K (f j) n x :=
  map_sum (cpushHom K I J n x) f s

end GlobalTheory.BiprodPush

end

noncomputable section

namespace GlobalTheory.BiprodPush

theorem injective_of_retracts {C : Type*} [Category C] [Preadditive C] {ι : Type} [Fintype ι] {X : C} (Y : ι → C)
    [∀ j, Injective (Y j)] (p : ∀ j, X ⟶ Y j) (i : ∀ j, Y j ⟶ X) (h : ∑ j, p j ≫ i j = 𝟙 X) : Injective X := by
  refine ⟨fun {A B} g m _ => ⟨∑ j, Injective.factorThru (g ≫ p j) m ≫ i j, ?_⟩⟩
  rw [Preadditive.comp_sum]
  simp_rw [← Category.assoc, Injective.comp_factorThru, Category.assoc, ← Preadditive.comp_sum, h, Category.comp_id]

theorem biproduct_push : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (g : ∀ j, L j ⟶ C) (m : ℤ), (∀ j, (L j).IsStrictlyGE m) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) n) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpush K (g j) n (a j) := by
  intro R _ ι _ L C g m hL hI
  classical
  haveI : HasFiniteBiproducts (Cx R) := HasFiniteBiproducts.of_hasFiniteProducts
  have htot : ∀ n, ∑ j, (biproduct.π L j).f n ≫ (biproduct.ι L j).f n = 𝟙 ((⨁ L).X n) := by
    intro n
    have := (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_sum (fun j => biproduct.π L j ≫ biproduct.ι L j) Finset.univ
    rw [biproduct.total] at this
    simp only [Functor.map_id, Functor.map_comp, HomologicalComplex.eval_map] at this
    exact this.symm
  refine ⟨⨁ L, biproduct.desc g, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero, ← htot i]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : IsZero ((L j).X i) := (L j).isZero_of_isStrictlyGE m i hi
    rw [show (biproduct.π L j).f i = 0 from this.eq_of_tgt _ _, zero_comp]
  · intro n
    exact injective_of_retracts (fun j => (L j).X n) (fun j => (biproduct.π L j).f n) (fun j => (biproduct.ι L j).f n) (htot n)
  · intro K n
    refine ⟨{ toFun := fun a => ∑ j, cpush K (biproduct.ι L j) n (a j)
              invFun := fun b j => cpush K (biproduct.π L j) n b
              left_inv := ?_
              right_inv := ?_ }, ?_⟩
    · intro a
      funext k
      simp only [map_sum, ← cpush_comp]
      rw [Finset.sum_eq_single k]
      · rw [biproduct.ι_π_self, cpush_id]
      · intro j _ hj
        rw [biproduct.ι_π_ne _ hj, cpush_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    · intro b
      simp only [← cpush_comp]
      rw [← cpush_sum, biproduct.total, cpush_id]
    · intro a
      change cpush K (biproduct.desc g) n (∑ j, cpush K (biproduct.ι L j) n (a j)) = _
      rw [map_sum]
      simp only [← cpush_comp, biproduct.ι_desc]

end GlobalTheory.BiprodPush

end
