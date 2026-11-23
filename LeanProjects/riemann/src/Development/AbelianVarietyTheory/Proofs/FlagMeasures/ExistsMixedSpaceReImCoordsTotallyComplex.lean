import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

open NumberField.InfinitePlace

def cxPlaceEquiv (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    {w : InfinitePlace E // IsComplex w} ≃ InfinitePlace E :=
  Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w

def mixedCoords (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    mixedEmbedding.mixedSpace E ≃ₗ[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)) where
  toFun x := (fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).re,
    fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).im)
  invFun y := (fun w => absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)),
    fun w => ⟨y.1 w.1, y.2 w.1⟩)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
    · apply Complex.ext <;> rfl
  right_inv y := rfl

private theorem measurePreserving_mixedSpace_snd (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    MeasurePreserving (Prod.snd : mixedEmbedding.mixedSpace E → ({w : InfinitePlace E // IsComplex w} → ℂ))
      volume volume := by
  have : IsEmpty {w : InfinitePlace E // IsReal w} :=
    ⟨fun w => not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2⟩
  have h : (volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)) = Measure.dirac 0 := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨measurable_snd, ?_⟩
  show Measure.map Prod.snd ((volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)).prod volume) = volume
  rw [h, Measure.map_snd_prod]
  simp

theorem measurePreserving_mixedCoords (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    MeasurePreserving (mixedCoords E) volume volume := by
  have h2 := measurePreserving_piCongrLeft (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (cxPlaceEquiv E)
  have h3 := measurePreserving_pi (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (fun _ => (volume : Measure (ℝ × ℝ))) (fun _ => Complex.volume_preserving_equiv_real_prod)
  have h4 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)
    (fun _ => (volume : Measure ℝ)) (fun _ => (volume : Measure ℝ))
  have key := h4.comp (h3.comp (h2.comp (measurePreserving_mixedSpace_snd E)))
  have e : (⇑(mixedCoords E)) = ⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)) ∘
      (fun a i => Complex.measurableEquivRealProd (a i)) ∘
        ⇑(MeasurableEquiv.piCongrLeft (fun _ => ℂ) (cxPlaceEquiv E)) ∘ Prod.snd := by
    funext x
    ext w <;> rfl
  rw [e]
  exact key

theorem mixedCoords_mixedEmbedding (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (x : E) : mixedCoords E (mixedEmbedding E x) = (reV x, imV x) := by
  ext w <;> simp [mixedCoords, reV, imV, mixedEmbedding.mixedEmbedding_apply_isComplex]

theorem mixedSpace_reIm_coords : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E →
    ∃ e : mixedEmbedding.mixedSpace E ≃L[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)),
      MeasurePreserving e volume volume ∧ ∀ x : E, e (mixedEmbedding E x) = (reV x, imV x) := by
  intro E _ _ hE
  have := hE
  exact ⟨(mixedCoords E).toContinuousLinearEquiv, by
    simpa using measurePreserving_mixedCoords E, fun x => by
    simpa using mixedCoords_mixedEmbedding E x⟩

end GlobalTheory.SnMass.SkewVol
