import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApplyStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.FinChart

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem maDens_locPot_eq_dens (L : Fin D → MLine p σ) (c : AlgChart p σ D) {z : Fin D → ℂ}
    (hz : z ∈ c.finChart.target) :
    maDens (fun i y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      dens L c (c.finChart.symm z) := by
  have hr : c.e (c.finChart.symm z) = toV D z := c.e.right_inv hz
  have hH (i) : hessC (fun y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      ((2⁻¹ : ℝ) : ℂ) • c.hess (L i).φ (pick (L i).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) := by
    have hd := (L i).cInf.contDiffAt c (c.finChart.map_target hz)
      (mem_pick (L i).φ.isLB (c.finChart.symm z))
    rw [hr] at hd
    have e : (fun y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) = fun y => 2⁻¹ *
        ((fun v => (L i).φ.φ (pick (L i).φ.isLB (c.finChart.symm z)) (c.e.symm v)) ∘ toV D) y :=
      funext fun _ => div_eq_inv_mul _ _
    rw [e, hessC_const_mul', AlgChart.hess, hr, cHess_eq_hessC hd]
  have hτ (τ : Equiv.Perm (Fin D)) : (Matrix.of fun j l => (((2⁻¹ : ℝ) : ℂ) •
      c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z)) j l).det =
      (((2⁻¹ : ℝ) ^ D : ℝ) : ℂ) * (Matrix.of fun j l =>
      c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) j l).det := by
    refine (Matrix.det_smul (Matrix.of fun j l => c.hess (L (τ l)).φ
      (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) j l) ((2⁻¹ : ℝ) : ℂ)).trans ?_
    rw [Fintype.card_fin, Complex.ofReal_pow]
  have hf : (1 / (D.factorial : ℂ)) = ((1 / (D.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  have h0 : (D.factorial : ℝ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have h2 : (2 / Real.pi) ^ D * (2⁻¹ : ℝ) ^ D = (Real.pi ^ D)⁻¹ := by
    rw [← mul_pow, ← inv_pow]
    congr 1
    ring
  simp only [maDens, hH, ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, hτ, dens]
  rw [← Finset.mul_sum, hf, Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← h2]
  field_simp

variable {A : FinHolAtlas D (CxPts p σ)}

theorem locDens_locPot_eq_dens (L : Fin D → MLine p σ) (hA : IsAlgAtlas A) (j : Fin A.n)
    {z : Fin D → ℂ} (hz : z ∈ (A.chart j).target) : locDens A (fun i => (L i).φ.locPot) j z =
      dens L (hA.anRead.chart j) ((A.chart j).symm z) := by
  unfold locDens
  rw [hA.chart_eq j] at hz ⊢
  exact maDens_locPot_eq_dens L _ hz

theorem part_eq_lintegral_locDens [SecondCountableTopology (CxPts p σ)] (L : Fin D → MLine p σ)
    (hA : IsAlgAtlas A) (ε : ℤˣ) (j : Fin A.n) (S : Set (CxPts p σ)) (hS : MeasurableSet S)
    (hs : S ⊆ (A.chart j).source) : part L ε S =
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S,
        ENNReal.ofReal (max ((ε : ℤ) * locDens A (fun i => (L i).φ.locPot) j y) 0) := by
  have hl (y) := locDens_locPot_eq_dens L hA j (z := y)
  generalize locDens A (fun i => (L i).φ.locPot) j = d at hl ⊢
  rw [hA.chart_eq j] at hs hl ⊢
  set c := hA.anRead.chart j
  have hm := measurableSet_image c.e hS hs
  rw [GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply k X p σ D L ε c S hS hs,
    ← measurePreserving_toV.setLIntegral_comp_preimage_emb (toV D).toHomeomorph.measurableEmbedding]
  have e : c.e '' S = c.e.target ∩ c.e.symm ⁻¹' S := by
    rw [← c.e.image_source_inter_eq', inter_eq_right.2 (show S ⊆ c.e.source from hs)]
  rw [e] at hm ⊢
  refine setLIntegral_congr_fun (hm.preimage (toV D).continuous.measurable) fun y hy => ?_
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_le, max_eq_left, hl y hy.1]
  rfl

theorem int_eq_mInt (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (D : ℕ)
    (A : FinHolAtlas D (CxPts p σ)) (hA : IsAlgAtlas A) (L : Fin D → MLine p σ)
    (g : CxPts p σ → ℝ) (hg : Measurable g) :
    (Intg L g ↔ MIntegrable A (fun i => (L i).φ.locPot) g) ∧
      (Intg L g → Mix.int L g = mInt A (fun i => (L i).φ.locPot) g) := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set P := hne.some
  set d := locDens A fun i => (L i).φ.locPot with hd
  have hdc (j) : ContinuousOn (d j) (A.chart j).target := locDensCont A _
    (fun i => ((Weight.isCInf_iff_isSmooth hA.anRead).1 (L i).cInf).isPotential hA) j
  let w (ε : ℤˣ) (j) (y) : ℝ := max ((ε : ℤ) * d j y) 0
  have hw (ε j) : ContinuousOn (w ε j) (A.chart j).target :=
    (continuous_id.max continuous_const).comp_continuousOn (continuousOn_const.mul (hdc j))
  have hw0 (ε j) : ∀ y ∈ (A.chart j).target, 0 ≤ w ε j y := fun _ _ => le_max_right _ _
  have hsub (j y) : w 1 j y - w (-1) j y = d j y := by
    simpa [w] using max_zero_sub_max_neg_zero_eq_self (d j y)
  have habs (ε j y) : |w ε j y| ≤ |d j y| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ((le_abs_self _).trans_eq ?_) (abs_nonneg _)
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have back (hm : MIntegrable A (fun i => (L i).φ.locPot) g) (ε j) : IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w ε j y)
      (A.chart j).target := by
    obtain ⟨hKc, hKs⟩ := image_closed_compact (A.chart j) (isClosed_tsupport (P.χ j))
      (P.tsupport_subset j)
    refine integrableOn_target_of_closed (A.chart j) (Z := tsupport (P.χ j))
      (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
    have hcc := (chi_comp_continuousOn P j).mono hKs
    refine Integrable.mono ((hm j _ hKs hKc).continuousOn_mul hcc hKc) ?_ (.of_forall fun y => ?_)
    · exact (((hcc.aemeasurable hKc.measurableSet).mul (hg.comp_aemeasurable
        (((A.chart j).continuousOn_symm.mono hKs).aemeasurable hKc.measurableSet))).mul
        (((hw ε j).mono hKs).aemeasurable hKc.measurableSet)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (habs ε j y) (by positivity)
  have pieces (hm : MIntegrable A (fun i => (L i).φ.locPot) g) (ε) :=
    integrable_of_pieces A P (hw ε) (hw0 ε) (part_eq_lintegral_locDens L hA ε) hg (back hm ε)
  have fwd (hi : Intg L g) : MIntegrable A (fun i => (L i).φ.locPot) g :=
    fun j K hK _ => by
    have key (ε) := (integrableOn_source_iff_of_density (A.chart j) (hw ε j) (hw0 ε j)
      (part_eq_lintegral_locDens L hA ε j) hg).1.1
    refine IntegrableOn.mono_set ?_ hK
    refine (Integrable.sub (key 1 hi.1.integrableOn) (key (-1) hi.2.integrableOn)).congr
      (.of_forall fun y => ?_)
    simp only [Pi.sub_apply, ← mul_sub, hsub, hd]
  refine ⟨⟨fwd, fun hm => ⟨(pieces hm 1).1, (pieces hm (-1)).1⟩⟩, fun hi => ?_⟩
  have hm := fwd hi
  rw [Mix.int, (pieces hm 1).2, (pieces hm (-1)).2,
    mInt_eq_integralWith A _ hne, integralWith, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (back hm 1 j) (back hm (-1) j)]
  simp only [← mul_sub, hsub, hd, P]

end GlobalTheory.Mix
