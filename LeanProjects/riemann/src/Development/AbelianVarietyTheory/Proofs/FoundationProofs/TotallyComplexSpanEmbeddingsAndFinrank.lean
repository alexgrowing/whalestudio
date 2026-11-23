import Mathlib
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

open NumberField.InfinitePlace NumberField.mixedEmbedding in

theorem totallyComplex_span_embeddings_and_finrank :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E],
      Submodule.span ℝ (Set.range (Pi.ringHom fun w : InfinitePlace E => w.embedding)) = ⊤ ∧
        Module.finrank ℝ (InfinitePlace E → ℂ) = Module.finrank ℚ E := by
  intro E _ _ _
  constructor
  ·
    let f : mixedSpace E →ₗ[ℝ] (InfinitePlace E → ℂ) :=
      { toFun := fun x w => x.2 ⟨w, IsTotallyComplex.isComplex w⟩
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    have hf : Function.Surjective f := by
      intro y
      exact ⟨(0, fun w => y w.1), rfl⟩
    have hcomp : ∀ x : E, f (mixedEmbedding E x) = Pi.ringHom (fun w : InfinitePlace E => w.embedding) x := by
      intro x
      funext w
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, mixedEmbedding_apply_isComplex]
      rfl
    have hspan : Submodule.span ℝ (Set.range (mixedEmbedding E)) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← (latticeBasis E).span_eq]
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (latticeBasis_apply E i).symm⟩
    have himg : f '' Set.range (mixedEmbedding E) =
        Set.range (Pi.ringHom fun w : InfinitePlace E => w.embedding) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hcomp)
    rw [← himg, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact hf
  · rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [IsTotallyComplex.finrank, card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    ring

end GlobalTheory
