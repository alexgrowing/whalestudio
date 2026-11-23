import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianWeightTotalMassStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaCompactDisjointRefinementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableLocalZeroCountStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem measurable_gW (d : ℕ) (α : Type) [Fintype α] : Measurable (gW d α) := by
  unfold gW
  fun_prop

theorem encard_iUnion_fin {X : Type} {m : ℕ} (B : Fin m → Set X)
    (h : Pairwise (Function.onFun Disjoint B)) :
    (((⋃ t, B t).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
  classical
  have key : ∀ s : Finset (Fin m), (((⋃ t ∈ s, B t).encard : ℕ∞) : ℝ≥0∞) =
      ∑ t ∈ s, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ENat.toENNReal_add,
        ih]
      exact Set.disjoint_iUnion₂_right.2 fun t ht => h (fun e => ha (e ▸ ht))
  simpa using key Finset.univ

theorem crofton : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∃ μ : Measure (Fin Y.dim → Fin n → ℂ), IsProbabilityMeasure μ ∧ μ ≪ volume ∧ (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ∫ C, (({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℝ) ∂μ := by
  intro Y Δ L r hL n b hb _
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  set φ := Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp) with hφdef
  have hφ : φ.IsCInf := Weight.isCInf_fsBasis hL b hb _ _
  have hneg : φ.chernPart Y.dim (-1) = 0 :=
    Weight.chernPart_neg_eq_zero hφ (Weight.semiPosReg_fsBasis hL b hb _ _)
  have hint := GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ
  have hfin : φ.chernPart Y.dim 1 Set.univ ≠ ⊤ := by
    have h1 := hint.1
    rw [IntegrableOn, Measure.restrict_univ, integrable_const_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 one_ne_zero
    · exact ((isFiniteMeasure_iff _).1 (by simpa using h1)).ne

  let ι := AlgChart Y.str (RingHom.id ℂ) Y.dim × L.ι × Fin n
  let S : ι → Set (CxPts Y.str (RingHom.id ℂ)) := fun t => t.1.e.source ∩
    (ptsIn Y.str (RingHom.id ℂ) (L.U t.2.1) ∩ ptsIn Y.str (RingHom.id ℂ) (nonzeroLocus (b t.2.2)))
  have hSo : ∀ t, IsOpen (S t) := fun t =>
    t.1.e.open_source.inter ((isOpen_ptsIn _).inter (isOpen_ptsIn _))
  have hSc : (⋃ t, S t) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := RingHom.id ℂ) y
    obtain ⟨j, hj⟩ := exists_mem_ptsIn hb y
    exact Set.mem_iUnion.2 ⟨⟨c, pick hL y, j⟩, hc, mem_pick hL y, hj⟩
  obtain ⟨m, l, A, hdis, hun, hsub, hσ⟩ := GlobalTheory.T.sigma_compact_disjoint_refinement _ ι S hSo hSc
  set G : ℝ≥0∞ := ENNReal.ofReal (Real.pi ^ (Y.dim * n)) with hG
  have hGpos : G ≠ 0 := by
    rw [hG, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hGtop : G ≠ ⊤ := ENNReal.ofReal_ne_top
  let Z : (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun C =>
    {y | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  let P : Fin m → (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun t C =>
    {y | y ∈ A t ∧ ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  have hpiece : ∀ t, Measurable (fun C => (((P t C).encard : ℕ∞) : ℝ≥0∞)) ∧
      ∫⁻ C, gW Y.dim (Fin n) C * (((P t C).encard : ℕ∞) : ℝ≥0∞) =
        G * φ.chernPart Y.dim 1 (A t) := fun t =>
    GlobalTheory.T.measurable_local_zero_count Y L hL n b hb (l t).1 (l t).2.1 (l t).2.2 (A t)
      (fun y hy => (hsub t hy).1) (fun y hy => (hsub t hy).2.1)
      (fun y hy => (secVal_ne_zero_iff _ (hsub t hy).2.1).2 (hsub t hy).2.2) (hσ t)
  have hZ : ∀ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((P t C).encard : ℕ∞) : ℝ≥0∞) := by
    intro C
    rw [← encard_iUnion_fin]
    · congr 2
      ext y
      simp only [Set.mem_iUnion, P, Z, Set.mem_setOf_eq]
      constructor
      · intro h
        obtain ⟨t, ht⟩ := Set.mem_iUnion.1 (hun ▸ Set.mem_univ y)
        exact ⟨t, ht, h⟩
      · rintro ⟨t, -, h⟩
        exact h
    · intro s t hst
      exact (hdis hst).mono (fun y hy => hy.1) (fun y hy => hy.1)
  have hNm : Measurable fun C => (((Z C).encard : ℕ∞) : ℝ≥0∞) := by
    simp only [hZ]
    exact Finset.measurable_fun_sum _ fun t _ => (hpiece t).1
  have hAm : ∀ t, MeasurableSet (A t) := fun t => by
    obtain ⟨K, hK, e⟩ := hσ t
    rw [← e]
    exact MeasurableSet.iUnion fun i => (hK i).measurableSet
  have hmass : φ.chernPart Y.dim 1 Set.univ = ∑ t, φ.chernPart Y.dim 1 (A t) := by
    rw [← hun, measure_iUnion hdis hAm, tsum_fintype]
  have hgm := measurable_gW Y.dim (Fin n)
  have hsum : ∫⁻ C, gW Y.dim (Fin n) C * (((Z C).encard : ℕ∞) : ℝ≥0∞) =
      G * φ.chernPart Y.dim 1 Set.univ := by
    simp only [hZ, Finset.mul_sum]
    rw [lintegral_finset_sum Finset.univ (f := fun t C => gW Y.dim (Fin n) C *
      (((P t C).encard : ℕ∞) : ℝ≥0∞)) fun t _ => hgm.mul (hpiece t).1, hmass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => (hpiece t).2
  let μ : Measure (Fin Y.dim → Fin n → ℂ) := G⁻¹ • volume.withDensity (gW Y.dim (Fin n))
  have hlin : ∀ f : (Fin Y.dim → Fin n → ℂ) → ℝ≥0∞, Measurable f →
      ∫⁻ C, f C ∂μ = G⁻¹ * ∫⁻ C, gW Y.dim (Fin n) C * f C := by
    intro f hf
    rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hgm hf]
    rfl
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have h1 := hlin (fun _ => 1) measurable_const
    simp only [lintegral_one, mul_one] at h1
    rw [h1, GlobalTheory.T.gaussian_weight_total_mass, Fintype.card_fin]
    exact ENNReal.inv_mul_cancel hGpos hGtop
  have hN : ∫⁻ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) ∂μ = φ.chernPart Y.dim 1 Set.univ := by
    rw [hlin _ hNm, hsum, ← mul_assoc, ENNReal.inv_mul_cancel hGpos hGtop, one_mul]
  refine ⟨μ, hprob, ?_, ?_⟩
  · exact (withDensity_absolutelyContinuous _ _).smul_left _
  · have hcast : ∀ C, ((Z C).ncard : ℝ) = ((((Z C).encard : ℕ∞) : ℝ≥0∞)).toReal := by
      intro C
      rw [Set.ncard]
      cases h : (Z C).encard with
      | top => simp
      | coe a => simp
    have hae : ∀ᵐ C ∂μ, (((Z C).encard : ℕ∞) : ℝ≥0∞) < ⊤ :=
      ae_lt_top hNm (by rw [hN]; exact hfin)
    have e := integral_toReal hNm.aemeasurable hae
    rw [hN] at e
    simp only [Z] at hcast e
    simp only [hcast]
    rw [e, Weight.chernInt, hneg]
    simp [Measure.real]
end GlobalTheory.CompanionTheory.FSCrofton
