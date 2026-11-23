import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.AeqCont

theorem null_preimage_lmulM {k r : ℕ} {μG : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μG)
    {s : Mat k r} (hs : s ∈ GG k r) {N : Set (Mt k r)} (hN : μG N = 0) :
    μG (lmulM s ⁻¹' N) = 0 := by
  have hm : Measurable (lmulM s : Mt k r → Mt k r) :=
    Continuous.measurable (α := Mt k r) (γ := Mt k r)
      (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  refine le_antisymm ?_ bot_le
  calc μG (lmulM s ⁻¹' N) ≤ μG (lmulM s ⁻¹' toMeasurable μG N) :=
        measure_mono (Set.preimage_mono (subset_toMeasurable μG N))
    _ = (μG.map (lmulM s)) (toMeasurable μG N) :=
        (Measure.map_apply hm (measurableSet_toMeasurable μG N)).symm
    _ = μG (toMeasurable μG N) := by rw [hμ.2.2.2 s hs]
    _ = 0 := by rw [measure_toMeasurable, hN]

theorem eqOn_of_ae (k r : ℕ) {B : Type} [NormedAddCommGroup B] (μG : Measure (Mt k r))
    (f g : Mat k r → B) (hμ : IsHaarOn (GG k r) μG) (hf : ContinuousOn f (GG k r))
    (hg : ContinuousOn g (GG k r))
    (hfg : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => g (Matrix.of x))) :
    ∀ x ∈ GG k r, f x = g x := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ _ hH
  intro x0 hx0
  by_contra hne
  obtain ⟨U, hUo, hU⟩ := (continuousOn_iff'.1 (hf.sub hg)) ({0}ᶜ : Set B) isOpen_compl_singleton
  have hmemU : ∀ y ∈ GG k r, y ∈ U → f y ≠ g y := by
    intro y hy hyU h
    have : y ∈ (f - g) ⁻¹' ({0}ᶜ : Set B) ∩ GG k r := by rw [hU]; exact ⟨hyU, hy⟩
    exact this.1 (by simp [h])
  have hx0U : x0 ∈ U := by
    have : x0 ∈ (f - g) ⁻¹' ({0}ᶜ : Set B) ∩ GG k r :=
      ⟨by simpa [sub_eq_zero] using hne, hx0⟩
    rw [hU] at this; exact this.1
  set N : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ U ∧ (Matrix.of x : Mat k r) ∈ GG k r} with hNdef
  have hN : μG N = 0 := by
    have h0 : μG {x | ¬ f (Matrix.of x) = g (Matrix.of x)} = 0 := ae_iff.1 hfg
    exact measure_mono_null (fun x hx => hmemU _ hx.2 hx.1) h0
  let O : GG k r → Set (Mt k r) := fun s => {x | (s.1 * Matrix.of x : Mat k r) ∈ U}
  have hO : ∀ s, IsOpen (O s) := fun s =>
    hUo.preimage (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  have hcov : {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} ⊆ ⋃ s ∈ T, lmulM s.1 ⁻¹' N := by
    intro x hx
    have hdet : IsUnit (Matrix.of x : Mat k r).det := (hgrp.2.2 _ hx).1
    have hxinv : (Matrix.of x : Mat k r)⁻¹ ∈ GG k r := (hgrp.2.2 _ hx).2
    let s : GG k r := ⟨x0 * (Matrix.of x : Mat k r)⁻¹, hgrp.2.1 _ hx0 _ hxinv⟩
    have hxO : x ∈ ⋃ i, O i := Set.mem_iUnion.2 ⟨s, by
      show x0 * (Matrix.of x : Mat k r)⁻¹ * Matrix.of x ∈ U
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]; exact hx0U⟩
    rw [← hT] at hxO
    obtain ⟨t, htT, hxt⟩ := Set.mem_iUnion₂.1 hxO
    exact Set.mem_iUnion₂.2 ⟨t, htT, hxt, hgrp.2.1 _ t.2 _ hx⟩
  have hG0 : μG {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} = 0 :=
    measure_mono_null hcov ((measure_biUnion_null_iff hTc).2 fun s _ => null_preimage_lmulM hμ s.2 hN)
  have huniv : μG Set.univ = 0 := by
    have : (Set.univ : Set (Mt k r)) =
        {x | (Matrix.of x : Mat k r) ∈ GG k r} ∪ {x | (Matrix.of x : Mat k r) ∉ GG k r} := by
      ext x; by_cases h : (Matrix.of x : Mat k r) ∈ GG k r <;> simp [h]
    rw [this]; exact measure_union_null hG0 hμ.2.2.1
  exact hμ.2.1 (Measure.measure_univ_eq_zero.1 huniv)

end GlobalTheory.SgInf.AeqCont
