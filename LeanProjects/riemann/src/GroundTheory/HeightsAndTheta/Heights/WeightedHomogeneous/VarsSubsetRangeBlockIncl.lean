import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem blockIncl_injective (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  simp only [blockIncl, Sigma.mk.injEq, heq_eq_eq, true_and] at h
  subst h; rfl

omit [Fintype ι] [DecidableEq ι] in

theorem evalCone_rename_blockIncl {F : Type*} [CommRing F] (k₀ : ι) (z : Cone n F)
    (f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ) :
    evalCone z (rename (blockIncl k₀) f') = evalCone (projBlock k₀ z) f' := by
  unfold evalCone
  rw [eval₂_rename]
  rfl

omit [Fintype ι] in

theorem vars_subset_range_blockIncl (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    (f.vars : Set (Coord n)) ⊆ Set.range (blockIncl k₀) := by
  classical
  intro v hv
  obtain ⟨d, hd, hdv⟩ := (mem_vars_iff_mem_support v).mp hv
  have hle : coordDeg n v ≤ Finsupp.weight (coordDeg n) d :=
    Finsupp.le_weight_of_ne_zero' (coordDeg n) (Finsupp.mem_support_iff.mp hdv)
  rw [hf (mem_support_iff.mp hd)] at hle
  have h1 := hle v.1
  obtain ⟨k, i⟩ := v
  by_cases hk : k = k₀
  · subst hk
    exact ⟨⟨(), i⟩, rfl⟩
  · simp [coordDeg, hk] at h1

omit [Fintype ι] in

theorem exists_blockForm (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ n k₀)) f' (fun _ ↦ m) ∧
        rename (blockIncl k₀) f' = f := by
  classical
  obtain ⟨f', rfl⟩ := exists_rename_eq_of_vars_subset_range f (blockIncl k₀)
    (blockIncl_injective k₀) (vars_subset_range_blockIncl k₀ m f hf)
  refine ⟨f', fun d hd ↦ ?_, rfl⟩
  have hmem : Finsupp.mapDomain (blockIncl k₀) d ∈ (rename (blockIncl k₀) f').support := by
    rw [support_rename_of_injective (blockIncl_injective k₀)]
    exact Finset.mem_image_of_mem _ (mem_support_iff.mpr hd)
  have hw := hf (mem_support_iff.mp hmem)
  have hw' : Finsupp.weight (coordDeg n) (Finsupp.mapDomain (blockIncl k₀) d) =
      Finsupp.degree d • Pi.single k₀ 1 := by
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) ↦ c • coordDeg n i)
      (fun _ ↦ zero_smul ℕ _) (fun _ _ _ ↦ add_smul _ _ _)]
    simp only [Finsupp.sum, coordDeg, blockIncl]
    rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from rfl, Finset.sum_smul]
  rw [hw'] at hw
  have hdeg : Finsupp.degree d = m := by
    simpa using congrFun hw k₀
  funext u
  rw [Finsupp.weight_apply]
  simp [Finsupp.sum, coordDeg, Finsupp.degree] at hdeg ⊢
  exact hdeg

theorem SupNormEquality.proof (hOnto : BlockSurjectivity.Statement) : SupNormEquality.Statement := by
  intro ι _ _ n P k₀ m
  refine ⟨fun f hf ↦ exists_blockForm k₀ m f hf, fun f' _ B ↦ ⟨fun h z' hz' ↦ ?_, fun h z hz ↦ ?_⟩⟩
  · rw [← hOnto ι n P k₀] at hz'
    obtain ⟨z, hz, rfl⟩ := hz'
    simpa [evalCone_rename_blockIncl, projBlock] using h z hz
  · have hz' : projBlock k₀ z ∈ conePoints (P.projIdeal k₀) ℂ := by
      rw [← hOnto ι n P k₀]; exact ⟨z, hz, rfl⟩
    simpa [evalCone_rename_blockIncl, projBlock] using h _ hz'

end

end GroundTheory.Heights₂.Heights
