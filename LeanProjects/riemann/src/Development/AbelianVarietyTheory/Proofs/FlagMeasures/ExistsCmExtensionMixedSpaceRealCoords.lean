import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.ReCoords

theorem comap_bij (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2) :
    Function.Bijective fun w : InfinitePlace E => w.comap (algebraMap F E) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨InfinitePlace.comap_surjective (k := F) (K := E), ?_⟩
  have h1 := IsTotallyComplex.finrank E
  have h2' := IsTotallyReal.finrank F
  have h3 := Module.finrank_mul_finrank ℚ F E
  rw [h2] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, IsTotallyReal.nrComplexPlaces_eq_zero F]
  omega

theorem re_embedding_comap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace E) (y : F) :
    ((w.comap (algebraMap F E)).embedding y).re = (w.embedding (algebraMap F E y)).re := by
  have key : ∀ φ : E →+* ℂ, (((InfinitePlace.mk φ).comap (algebraMap F E)).embedding y).re = (φ (algebraMap F E y)).re := by
    intro φ
    rw [InfinitePlace.comap_mk]
    rcases InfinitePlace.embedding_mk_eq (φ.comp (algebraMap F E)) with h | h
    · rw [h]; rfl
    · rw [h]; simp [ComplexEmbedding.conjugate_coe_eq]
  have := key w.embedding
  rwa [InfinitePlace.mk_embedding] at this

theorem mixedSpace_reCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : mixedEmbedding.mixedSpace F ≃L[ℝ] (InfinitePlace E → ℝ), MeasurePreserving e volume volume ∧ ∀ y : F, e (mixedEmbedding F y) = reV (algebraMap F E y) := by
  intro F E _ _ _ _ _ σ h
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  haveI : IsEmpty {w : InfinitePlace F // InfinitePlace.IsComplex w} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  let g : InfinitePlace E ≃ {v : InfinitePlace F // InfinitePlace.IsReal v} :=
    (Equiv.ofBijective _ (comap_bij F E h.2.2.1)).trans
      (Equiv.subtypeUnivEquiv (fun v : InfinitePlace F => IsTotallyReal.isReal v)).symm
  have hg : ∀ w, (g w).1 = w.comap (algebraMap F E) := fun w => rfl
  let L : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace E → ℝ) :=
    { toFun := fun x w => x.1 (g w)
      invFun := fun f => (fun v => f (g.symm v), 0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun x => Prod.ext (funext fun v => by simp) (Subsingleton.elim _ _)
      right_inv := fun f => funext fun w => by simp }
  refine ⟨L.toContinuousLinearEquiv, ?_, ?_⟩
  · haveI : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace F // InfinitePlace.IsComplex w} → ℂ)) := by
      rw [volume_pi, Measure.pi_of_empty]; infer_instance
    have h1 : MeasurePreserving (Prod.fst : mixedEmbedding.mixedSpace F → _) volume volume :=
      measurePreserving_fst
    have h2 := volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace E => ℝ) g.symm
    have heq : (L.toContinuousLinearEquiv : mixedEmbedding.mixedSpace F → InfinitePlace E → ℝ) =
        (MeasurableEquiv.piCongrLeft (fun _ : InfinitePlace E => ℝ) g.symm) ∘ Prod.fst := by
      funext x w
      simp [L, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rw [heq]
    exact h2.comp h1
  · intro y
    funext w
    show (mixedEmbedding F y).1 (g w) = _
    rw [mixedEmbedding.mixedEmbedding_apply_isReal, reV]
    rw [← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ y), InfinitePlace.embedding_of_isReal_apply, hg]
    exact re_embedding_comap w y

end GlobalTheory.SnMass.ReCoords
