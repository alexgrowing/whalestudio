import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem filtered_identify_pairs {J : Type} [SmallCategory J] [IsFiltered J] (P : J ⥤ Type)
    (Q : Type) (ι : ∀ j, P.obj j → Q)
    (hinj : ∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y)
    (j : J) (T : Finset (P.obj j × P.obj j)) (hT : ∀ p ∈ T, ι j p.1 = ι j p.2) :
    ∃ (k : J) (f : j ⟶ k), ∀ p ∈ T, P.map f p.1 = P.map f p.2 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | @insert p T hp ih =>
    obtain ⟨k1, f1, h1⟩ := ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    obtain ⟨k2, f2, h2⟩ := hinj j p.1 p.2 (hT p (Finset.mem_insert_self p T))
    have e : f1 ≫ IsFiltered.leftToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2) =
        f2 ≫ IsFiltered.rightToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2) := by
      simpa only [Category.assoc] using
        IsFiltered.coeq_condition (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2)
    refine ⟨_, f1 ≫ IsFiltered.leftToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2), ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [e]
      simp only [FunctorToTypes.map_comp_apply, h2]
    · simp only [FunctorToTypes.map_comp_apply, h1 q hq]

theorem finsupp_mapDomain_eq_zero_at_stage (Λ : Type 1) [AddCommGroup Λ] (J : Type)
    [SmallCategory J] [IsFiltered J] (P : J ⥤ Type) (Q : Type) (ι : ∀ j, P.obj j → Q)
    (hcompat : ∀ (j k : J) (f : j ⟶ k) (x : P.obj j), ι k (P.map f x) = ι j x)
    (hinj : ∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y)
    (j : J) (x : P.obj j →₀ Λ) (hx : Finsupp.mapDomain (ι j) x = 0) :
    ∃ (k : J) (f : j ⟶ k), Finsupp.mapDomain (P.map f) x = 0 := by
  classical
  obtain ⟨k, f, hf⟩ := filtered_identify_pairs P Q ι hinj j
    ((x.support ×ˢ x.support).filter (fun p => ι j p.1 = ι j p.2))
    (fun p hp => (Finset.mem_filter.mp hp).2)
  refine ⟨k, f, ?_⟩
  have hcomp : Finsupp.mapDomain (ι k) (Finsupp.mapDomain (P.map f) x) =
      Finsupp.mapDomain (ι j) x := by
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext a
    exact hcompat j k f a
  have hInj : Set.InjOn (ι k) (P.map f '' (x.support : Set (P.obj j))) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hcompat, hcompat] at hab
    exact hf (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩)
  apply Finsupp.mapDomain_injOn _ hInj
  · intro b hb
    have := Finsupp.mapDomain_support (f := P.map f) (s := x) hb
    simpa using this
  · simp
  · rw [hcomp, hx, Finsupp.mapDomain_zero]

end GlobalTheory
