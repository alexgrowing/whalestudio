import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTranscRatioDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LinearIndependentAdjoinOfTranscendental
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem TranscRatioDeg.proof : TranscRatioDeg.Statement := by
  intro ι E _ _ u D e w i₀ Φ _ _ hi₀ he hw ht hΦ
  have ht0 : w 0 ≠ 0 := by
    intro h0
    apply ht
    rw [h0]
    exact isAlgebraic_zero
  have hwk : ∀ k, w k = w 0 * (u (e k) / u (e 0)) := fun k => by
    rw [mul_div_assoc', ← hw k, mul_div_cancel_right₀ _ (he 0)]

  have hfn : ∀ {κ : Type} (v : κ → E) (K : Subfield E), (∀ i j, v i / v j ∈ K) →
      ∀ x ∈ fnField v, x ∈ K := by
    intro κ v K hK x hx
    have : (fnField v).toSubfield ≤ K := by
      unfold fnField
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro _ (⟨q, rfl⟩ | ⟨i, j, rfl⟩)
      · rw [eq_ratCast]
        exact SubfieldClass.ratCast_mem K q
      · exact hK i j
    exact this hx
  have hrat : ∀ i j, u i / u j ∈ fnField u := fun i j =>
    IntermediateField.subset_adjoin ℚ _ ⟨i, j, rfl⟩
  have hle : fnField (u ∘ e) ≤ fnField u := fun x hx =>
    hfn (u ∘ e) (fnField u).toSubfield (fun k l => hrat (e k) (e l)) x hx
  set F₀ := fnField (u ∘ e)
  set A := IntermediateField.extendScalars hle
  set L := IntermediateField.adjoin F₀ {w 0}

  have hL : ∀ x, x ∈ L ↔ x ∈ Subfield.closure (Set.range w) := by
    have h1 : L.toSubfield ≤ Subfield.closure (Set.range w) := by
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro _ (⟨⟨x, hx⟩, rfl⟩ | h)
      · refine hfn (u ∘ e) _ (fun k l => ?_) x hx
        have : (u ∘ e) k / (u ∘ e) l = w k / w l := by
          rw [hwk k, hwk l]
          field_simp [ht0, he 0, he l]
          simp only [Function.comp_apply]
          ring
        rw [this]
        exact div_mem (Subfield.subset_closure ⟨k, rfl⟩) (Subfield.subset_closure ⟨l, rfl⟩)
      · rw [Set.mem_singleton_iff.1 h]
        exact Subfield.subset_closure ⟨0, rfl⟩
    have h2 : Subfield.closure (Set.range w) ≤ L.toSubfield := by
      rw [Subfield.closure_le]
      rintro _ ⟨k, rfl⟩
      rw [hwk k]
      have hr : u (e k) / u (e 0) ∈ F₀ := IntermediateField.subset_adjoin ℚ _ ⟨k, 0, rfl⟩
      exact mul_mem (IntermediateField.mem_adjoin_simple_self F₀ (w 0))
        (IntermediateField.algebraMap_mem L (⟨_, hr⟩ : F₀))
    exact fun x => ⟨fun hx => h1 hx, fun hx => h2 hx⟩
  have hLset : Set.range (algebraMap L E) = (Subfield.closure (Set.range w) : Set E) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (hL _).1 y.2
    · intro hx
      exact ⟨⟨x, (hL x).2 hx⟩, rfl⟩

  have hQ : ∀ x ∈ fnField u, x ∈ Subfield.closure (Set.range u) := hfn u _ fun i j =>
    div_mem (Subfield.subset_closure ⟨i, rfl⟩) (Subfield.subset_closure ⟨j, rfl⟩)
  have htA : Transcendental A (w 0) :=
    TranscRatioDeg.transcendental_of_subfield (Subfield.closure (Set.range u)) (fun x => hQ _ x.2)
      (algebraMap A E).injective (TranscRatioDeg.transcendental_subfieldClosure u (w 0) ht)
  have key := TranscRatioDeg.finrank_adjoin_eq_of_transcendental A htA
  have hproj : projDeg u e = Module.finrank F₀ A := IntermediateField.relfinrank_eq_finrank_of_le hle
  rw [hproj, ← key]
  apply TranscRatioDeg.finrank_adjoin_congr
  · rw [hΦ]
    apply SetLike.ext'
    rw [RingHom.coe_fieldRange, hLset]
  · rw [← RingHom.coe_fieldRange, hΦ, hLset]
    apply le_antisymm
    · rw [Subfield.closure_le]
      rintro _ (h | ⟨i, rfl⟩)
      · exact Subfield.subset_closure (Or.inl h)
      · exact Subfield.subset_closure (Or.inr (hrat i i₀))
    · rw [Subfield.closure_le]
      rintro x (h | h)
      · exact Subfield.subset_closure (Or.inl h)
      · refine hfn u _ (fun i j => ?_) x h
        have : u i / u j = (u i / u i₀) / (u j / u i₀) := by
          rw [div_div_div_cancel_right₀ hi₀]
        rw [this]
        exact div_mem (Subfield.subset_closure (Or.inr ⟨i, rfl⟩))
          (Subfield.subset_closure (Or.inr ⟨j, rfl⟩))

end GroundTheory.Heights₂.Heights.HilbertSamuel
