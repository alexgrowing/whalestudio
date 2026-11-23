import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StValCentreZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.KerIsMultiHomogIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo regularityEmbedding_holds

noncomputable section

theorem ValCentreZ.proof : ValCentreZ.Statement := by
  intro K _ ι _ P hP
  have := hP.1
  intro R
  classical
  set L := FractionRing (MRing ι ⧸ P)
  have hX0 : ∀ {f : MRing ι}, f ∉ P → toFrac P f ≠ 0 := fun hf h => hf (toFrac_eq_zero.mp h)

  have hj : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι) ∉ P ∧
      ∀ i', R.valuation (toFrac P (X ⟨k, i'⟩)) ≤ R.valuation (toFrac P (X ⟨k, i⟩)) := by
    intro k
    obtain ⟨i₀, hi₀⟩ := hP.2.2 k
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => (X ⟨k, i⟩ : MRing ι) ∉ P)
      (fun i => R.valuation (toFrac P (X ⟨k, i⟩))) ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun i' => ?_⟩
    by_cases hi' : (X ⟨k, i'⟩ : MRing ι) ∈ P
    · rw [toFrac_eq_zero.mpr hi', map_zero]; exact zero_le
    · exact hmax i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)
  choose j hjP hjmax using hj
  choose r hr using fun p : Σ k, ι k =>
    exists_funField_mul_eq (P := P) (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 (j p.1)) (hjP p.1)

  have hrle : ∀ p, R.valuation (r p : L) ≤ 1 := by
    intro p
    have hvj : R.valuation (toFrac P (X ⟨p.1, j p.1⟩)) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]; exact hX0 (hjP p.1)
    have h := congrArg R.valuation (hr p)
    rw [map_mul] at h
    have hle : R.valuation (r p : L) * R.valuation (toFrac P (X ⟨p.1, j p.1⟩)) ≤
        1 * R.valuation (toFrac P (X ⟨p.1, j p.1⟩)) := by
      rw [one_mul]; exact (le_of_eq h).trans (hjmax p.1 p.2)
    exact le_of_mul_le_mul_right hle (zero_lt_iff.mpr hvj)

  have hmem : ∀ g, (chartHom r g : L) ∈ R := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => rw [chartHom_coe, eval₂Hom_C, eq_intCast]; exact intCast_mem R a
    | add f g hf hg => rw [map_add, Subring.coe_add]; exact add_mem hf hg
    | mul_X f p hf =>
      rw [map_mul, Subring.coe_mul]
      refine mul_mem hf ?_
      rw [← R.valuation_le_one_iff]
      simpa [chartHom] using hrle p

  obtain ⟨E, _, ψE, hψE⟩ : ∃ (E : Type) (_ : Field E) (ψE : MRing ι →+* E),
      ∀ g, ψE g = 0 ↔ R.valuation (chartHom r g : L) < 1 := by
    refine ⟨IsLocalRing.ResidueField R, inferInstance,
      (IsLocalRing.residue R).comp (((funField P).subtype.comp (chartHom r)).codRestrict R hmem), fun g => ?_⟩
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff]
    exact Iff.rfl

  have hform : ∀ (g : MRing ι) (a : K → ℕ), IsMultiHomog g a →
      (g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ R.valuation (chartHom r g : L) < 1) := by
    intro g a hg
    rw [RingHom.mem_ker, RegularityFunctionFieldNumber.specMap_form ψE ∅ hg, ← hψE, mul_eq_zero, MvPolynomial.C_eq_zero]
    refine or_iff_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_)
    simp [RegularityFunctionFieldNumber.cS, MvPolynomial.X_ne_zero]
  have hPW : P ≤ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1
    refine hPS.le.trans (Ideal.span_le.mpr fun g hg => ?_)
    obtain ⟨a, ha⟩ := hS g hg
    have hgP : g ∈ P := hPS ▸ Ideal.subset_span hg
    rw [SetLike.mem_coe, hform g a ha]
    have h1 := chartHom_mul j r hr ha
    rw [toFrac_eq_zero.mpr hgP] at h1
    rw [(mul_eq_zero.mp h1).resolve_right (toFrac_prod_ne_zero j hjP a), map_zero]
    exact zero_lt_one
  refine ⟨RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅),
    ⟨RingHom.ker_isPrime _, RegularityValuationCentre.ker_isMultiHomogIdeal ψE, fun k => ⟨j k, ?_⟩⟩, hPW, ?_⟩
  ·
    have hrj : (r ⟨k, j k⟩ : L) = 1 :=
      mul_right_cancel₀ (hX0 (hjP k)) ((hr ⟨k, j k⟩).trans (one_mul _).symm)
    rw [hform _ _ (isMultiHomog_X_single k (j k))]
    have hXr : chartHom r (X ⟨k, j k⟩) = r ⟨k, j k⟩ := eval₂Hom_X' _ _ _
    rw [hXr, hrj, Valuation.map_one]
    exact lt_irrefl 1
  ·
    intro b f g hf hg hgW
    have hM := toFrac_prod_ne_zero j hjP b
    have e : toFrac P f / toFrac P g = (chartHom r f : L) / (chartHom r g : L) := by
      rw [← chartHom_mul j r hr hf, ← chartHom_mul j r hr hg, mul_div_mul_right _ _ hM]
    have hvg : R.valuation (chartHom r g : L) = 1 :=
      le_antisymm ((R.valuation_le_one_iff _).mpr (hmem g)) (not_lt.mp fun h => hgW ((hform g b hg).mpr h))
    change toFrac P f / toFrac P g ∈ R ∧
      (f ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ toFrac P f / toFrac P g ∈ R.nonunits)
    rw [e, ValuationSubring.mem_nonunits_iff, map_div₀, hvg, div_one, hform f b hf]
    refine ⟨(R.valuation_le_one_iff _).mp ?_, Iff.rfl⟩
    rw [map_div₀, hvg, div_one]
    exact (R.valuation_le_one_iff _).mpr (hmem f)

end

end GroundTheory.Heights₂.Heights.Inter
