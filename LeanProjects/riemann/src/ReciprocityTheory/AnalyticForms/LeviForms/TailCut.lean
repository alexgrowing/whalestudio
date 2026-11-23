import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

open Filter Topology LeviFormBoundaryTopology
open scoped ContDiff

def RWGeStatement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (L : LocPot X) (s : X → X → ℂ),
    (∀ y, logNormSec L s y ≤ 0) → ∀ y, Real.exp 1 ≤ rW L s y

theorem rW_ge : RWGeStatement := by
  intro X _ L s h y
  have hy := h y
  unfold rW
  linarith

def BdryNullStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → maMeasure A Φ (bdry s) = 0

private lemma continuousAt_of_continuousOn_chart_comp {e : ℕ} {X β : Type} [TopologicalSpace X] [TopologicalSpace β]
    (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {f : X → β}
    (hf : ∀ j, ContinuousOn (f ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {y : X} (hy : y ∈ U) : ContinuousAt f y := by
  obtain ⟨j, hj⟩ := A.cover y
  have hmem : (A.chart j) y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) y) ∈ U
    rw [(A.chart j).left_inv hj]
    exact hy
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) ((A.chart j) y) :=
    (hf j).continuousAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hmem)
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) y :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp only [Function.comp_apply, (A.chart j).left_inv hz]

private lemma isClosed_bdry_of_isSection' {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hs : IsSection A L s) :
    IsClosed (bdry s) := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hL1, _⟩ := hL
  have hN : Continuous (fun y => ‖s y y‖ * Real.exp (-L.φ y y)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have h1 : ContinuousAt (s y) y :=
      continuousAt_of_continuousOn_chart_comp A (L.isOpen_U y) (fun j => (hs1 y j).continuousOn) (L.mem_U y)
    have h2 : ContinuousAt (L.φ y) y :=
      continuousAt_of_continuousOn_chart_comp A (L.isOpen_U y) (fun j => (hL1 y j).continuousOn) (L.mem_U y)
    refine (h1.norm.mul h2.neg.rexp).congr ?_
    filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
    exact (hs2 z y z ⟨L.mem_U z, hz⟩).symm
  have hB : bdry s = (fun y => ‖s y y‖ * Real.exp (-L.φ y y)) ⁻¹' {0} := by
    ext y
    simp [bdry, Real.exp_ne_zero]
  rw [hB]
  exact isClosed_singleton.preimage hN

theorem bdry_null : BdryNullStatement := by
  intro e X _ _ _ _ _ A L s n m W hL hs hsnc Φ hΦ
  have hB : IsClosed (bdry s) := isClosed_bdry_of_isSection' A L s hL hs
  unfold maMeasure
  split_ifs with h
  swap
  · simp
  simp only [Measure.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  rw [Measure.map_apply_of_aemeasurable (((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac
    (withDensity_absolutelyContinuous _ _)) hB.measurableSet]
  have hnull : (volume.restrict (A.chart j).target) ((A.chart j).symm ⁻¹' bdry s) = 0 := by
    rw [Measure.restrict_apply' hT]
    apply measure_null_of_locally_null
    intro z hz
    obtain ⟨hzB, hzT⟩ := hz
    obtain ⟨ψ, hψc, hyψ, hψU, σ, -, -, uh, -, huh0, hfac⟩ := hsnc ((A.chart j).symm z)
    have hN : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
      (A.chart j).isOpen_inter_preimage_symm ψ.open_source
    refine ⟨((A.chart j).symm ⁻¹' bdry s ∩ (A.chart j).target) ∩
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source),
      inter_mem_nhdsWithin _ (hN.mem_nhds ⟨hzT, hyψ⟩), ?_⟩
    have hzero : ∀ y' ∈ ψ.source, y' ∈ bdry s → ∃ i, ψ y' i = 0 := by
      intro y' hy' hy'B
      have h1 := hs.2 y' ((A.chart j).symm z) y' ⟨L.mem_U y', hψU hy'⟩
      have h2 : s y' y' = 0 := hy'B
      rw [h2, norm_zero, zero_mul] at h1
      have h3 : s ((A.chart j).symm z) y' = 0 := by
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact norm_eq_zero.mp h
        · exact absurd h (Real.exp_ne_zero _)
      rw [hfac y' hy'] at h3
      have hprod := (mul_eq_zero.mp h3).resolve_left (huh0 y' hy')
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hprod
      rcases hσk : σ k with _ | i
      · simp [hσk] at hk
      · simp only [hσk] at hk
        refine ⟨i, ?_⟩
        by_contra hne
        exact pow_ne_zero _ hne hk
    have hsub : ((A.chart j).symm ⁻¹' bdry s ∩ (A.chart j).target) ∩
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) ⊆
        ⋃ i, ((A.chart j) ∘ ψ.symm) '' ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩ {p | p i = 0}) := by
      rintro z' ⟨⟨hz'B, hz'T⟩, -, hz'ψ⟩
      obtain ⟨i, hi⟩ := hzero _ hz'ψ hz'B
      refine Set.mem_iUnion.mpr ⟨i, ψ ((A.chart j).symm z'), ⟨⟨ψ.map_source hz'ψ, ?_⟩, hi⟩, ?_⟩
      · show ψ.symm (ψ ((A.chart j).symm z')) ∈ (A.chart j).source
        rw [ψ.left_inv hz'ψ]
        exact (A.chart j).map_target hz'T
      · show (A.chart j) (ψ.symm (ψ ((A.chart j).symm z'))) = z'
        rw [ψ.left_inv hz'ψ, (A.chart j).right_inv hz'T]
    refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
    have hdiff : DifferentiableOn ℝ ((A.chart j) ∘ ψ.symm)
        ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩ {p | p i = 0}) :=
      ((hψc j).2.differentiableOn.restrictScalars ℝ).mono Set.inter_subset_left
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff ?_
    refine measure_mono_null Set.inter_subset_right ?_
    exact Measure.pi_hyperplane _ i 0
  exact withDensity_absolutelyContinuous _ _ hnull

def RWOpenStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ), IsPotential A L → IsSection A L s →
      ContinuousOn (rW L s) (bdry s)ᶜ ∧ ∀ R : ℝ, IsOpen {y | y ∉ bdry s ∧ rW L s y < R}

theorem rW_open : RWOpenStatement := by
  intro e X _ A L s hL hs
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hL1, _⟩ := hL
  have hN : Continuous (fun y => ‖s y y‖ * Real.exp (-L.φ y y)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have h1 : ContinuousAt (s y) y :=
      continuousAt_of_continuousOn_chart_comp A (L.isOpen_U y) (fun j => (hs1 y j).continuousOn) (L.mem_U y)
    have h2 : ContinuousAt (L.φ y) y :=
      continuousAt_of_continuousOn_chart_comp A (L.isOpen_U y) (fun j => (hL1 y j).continuousOn) (L.mem_U y)
    refine (h1.norm.mul h2.neg.rexp).congr ?_
    filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
    exact (hs2 z y z ⟨L.mem_U z, hz⟩).symm
  have hB : (bdry s)ᶜ = (fun y => ‖s y y‖ * Real.exp (-L.φ y y)) ⁻¹' {0}ᶜ := by
    ext y
    simp [bdry, Real.exp_ne_zero]
  have hopen : IsOpen (bdry s)ᶜ := by
    rw [hB]
    exact isOpen_compl_singleton.preimage hN
  have hcont : ContinuousOn (rW L s) (bdry s)ᶜ := by
    have hne : ∀ y ∈ (bdry s)ᶜ, ‖s y y‖ * Real.exp (-L.φ y y) ≠ 0 := by
      intro y hy
      rw [hB] at hy
      exact hy
    show ContinuousOn (fun y => Real.exp 1 - 2 * Real.log (‖s y y‖ * Real.exp (-L.φ y y))) _
    exact continuousOn_const.sub (continuousOn_const.mul (hN.continuousOn.log hne))
  exact ⟨hcont, fun R => hcont.isOpen_inter_preimage hopen isOpen_Iio⟩

def CutoffStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ : LocPot X) (u : X → ℝ)
    (M : ℝ), IsPotential A Θ → IsPsh A Θ → A.Smooth u → IsPsh A (Θ + LocPot.ofFun u) →
    (∀ y, u y ≤ 0) → 0 ≤ M →
      let uR := fun y => ReciprocityTheory.AnForm.A.regMax 1 ![u y, -M] - 1 / 2
      A.Smooth uR ∧ IsPsh A (Θ + LocPot.ofFun uR) ∧ (∀ y, -M - 1 ≤ uR y ∧ uR y ≤ 0) ∧
        ∀ y, -M + 1 ≤ u y → uR y = u y - 1 / 2

theorem cutoff : CutoffStatement :=by
  intro e X _ A Θ u M hΘ hΘpsh hu hΘu hu0 hM uR
  obtain ⟨hR, -⟩ := ReciprocityTheory.AnForm.A.regMax_thm (Fin 2)
  obtain ⟨hcd, -, -, hb, hdom, -, htr, -⟩ := hR 1 one_pos
  have huR : ∀ y, uR y = ReciprocityTheory.AnForm.A.regMax 1 ![u y, -M] - 1 / 2 := fun _ => rfl
  have hvec : ∀ {S : Set (Fin e → ℂ)} {f g : (Fin e → ℂ) → ℝ}, ContDiffOn ℝ ∞ f S →
      ContDiffOn ℝ ∞ g S → ContDiffOn ℝ ∞ (fun y => ![f y, g y]) S := by
    intro S f g hf hg
    refine contDiffOn_pi.2 fun i => ?_
    fin_cases i
    · simpa using hf
    · simpa using hg
  refine ⟨fun j => ?_, ?_, fun y => ?_, fun y hy => ?_⟩
  · show ContDiffOn ℝ ∞ (fun z => ReciprocityTheory.AnForm.A.regMax 1 ![u ((A.chart j).symm z), -M] - 1 / 2) _
    exact (hcd.comp_contDiffOn (hvec (hu j) contDiffOn_const)).sub contDiffOn_const
  · intro x j y hy w
    set c := A.chart j with hc
    let F0 : (Fin e → ℂ) → ℝ := fun z => Θ.φ x (c.symm z) + u (c.symm z)
    let F1 : (Fin e → ℂ) → ℝ := fun z => Θ.φ x (c.symm z) - M
    have heq : ((Θ + LocPot.ofFun uR).φ x ∘ c.symm) =
        fun z => ReciprocityTheory.AnForm.A.regMax 1 (fun k => ![F0, F1] k z) - 1 / 2 := by
      funext z
      show Θ.φ x (c.symm z) + (ReciprocityTheory.AnForm.A.regMax 1 ![u (c.symm z), -M] - 1 / 2) = _
      have h2 : (fun k => ![F0, F1] k z) = fun k => ![u (c.symm z), -M] k + Θ.φ x (c.symm z) := by
        funext k
        fin_cases k
        · simp [F0]; ring
        · simp [F1]; ring
      rw [h2, htr]
      ring
    rw [heq, levi_sub_const]
    have hU : IsOpen (c.target ∩ c.symm ⁻¹' Θ.U x) := c.isOpen_inter_preimage_symm (Θ.isOpen_U x)
    have hyU : y ∈ c.target ∩ c.symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.1⟩
    have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hsm : ∀ k, ContDiffOn ℝ 2 (![F0, F1] k) (c.target ∩ c.symm ⁻¹' Θ.U x) := by
      intro k
      fin_cases k
      · exact (((hΘ.1 x j).add ((hu j).mono fun z hz => ⟨hz.1, trivial⟩))).of_le h2le
      · exact ((hΘ.1 x j).sub contDiffOn_const).of_le h2le
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm e (Fin 2) 1 _ (![F0, F1]) hU one_pos hsm y hyU w 0 ?_
    intro k
    fin_cases k
    · exact hΘu x j y hy w
    · show 0 ≤ levi (fun z => Θ.φ x (c.symm z) - M) y w
      rw [levi_sub_const]
      exact hΘpsh x j y hyU w
  · obtain ⟨h1, h2⟩ := hb ![u y, -M]
    have hge : -M ≤ ReciprocityTheory.AnForm.A.tmax ![u y, -M] := ReciprocityTheory.AnForm.A.le_tmax ![u y, -M] 1
    have hle : ReciprocityTheory.AnForm.A.tmax ![u y, -M] ≤ 0 := by
      refine ReciprocityTheory.AnForm.A.tmax_le fun k => ?_
      fin_cases k
      · simpa using hu0 y
      · simpa using hM
    rw [huR]
    constructor <;> linarith
  · rw [huR, hdom ![u y, -M] 0 ?_]
    · simp
    · intro k hk
      fin_cases k
      · exact absurd rfl hk
      · simp; linarith

def MaMeasureCongrOpenStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : FinHolAtlas e X) (Θ : Fin e → LocPot X) (u v : Fin e → X → ℝ) (V : Set X), IsOpen V →
    (∀ i, ∃ c : ℝ, ∀ y ∈ V, v i y = u i y + c) →
      (maMeasure A (fun i => Θ i + LocPot.ofFun (u i))).restrict V =
        (maMeasure A (fun i => Θ i + LocPot.ofFun (v i))).restrict V

private lemma maDens_congr_of_hessC_eq {D : ℕ} (F G : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (c : Fin D → ℝ) (h : ∀ k, G k =ᶠ[𝓝 z] fun y => F k y + c k) : maDens G z = maDens F z := by
  have hk : ∀ k, hessC (G k) z = hessC (F k) z := by
    intro k
    have h2 : fderiv ℝ (G k) =ᶠ[𝓝 z] fderiv ℝ (F k) := by
      filter_upwards [(h k).eventuallyEq_nhds] with y hy
      rw [hy.fderiv_eq, fderiv_add_const]
    unfold hessC
    rw [h2.fderiv_eq]
  unfold maDens
  simp only [hk]

theorem maMeasure_congr_open : MaMeasureCongrOpenStatement := by
  intro e X _ _ _ A Θ u v V hV hc
  choose c hc using hc
  have hloc : ∀ j, ∀ z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V,
      locDens A (fun i => Θ i + LocPot.ofFun (u i)) j z =
        locDens A (fun i => Θ i + LocPot.ofFun (v i)) j z := by
    intro j z hz
    have hW : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) :=
      (A.chart j).isOpen_inter_preimage_symm hV
    unfold locDens
    symm
    apply maDens_congr_of_hessC_eq _ _ z c
    intro k
    filter_upwards [hW.mem_nhds hz] with y hy
    show (Θ k).φ _ _ + v k _ = (Θ k).φ _ _ + u k _ + c k
    rw [hc k _ hy.2]
    ring
  unfold maMeasure
  split_ifs with h
  · ext t ht
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    simp only [Measure.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
    have hW : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) :=
      (A.chart j).isOpen_inter_preimage_symm hV
    have hae : ∀ f : (Fin e → ℂ) → ENNReal,
        AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity f) :=
      fun f => ((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [Measure.map_apply_of_aemeasurable (hae _) (ht.inter hV.measurableSet),
      Measure.map_apply_of_aemeasurable (hae _) (ht.inter hV.measurableSet),
      withDensity_apply', withDensity_apply']
    apply lintegral_congr_ae
    have hsub : (A.chart j).symm ⁻¹' (t ∩ V) ⊆
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) ∪ (A.chart j).targetᶜ := by
      intro a ha
      by_cases haT : a ∈ (A.chart j).target
      · exact Or.inl ⟨haT, ha.2⟩
      · exact Or.inr haT
    refine ae_restrict_of_ae_restrict_of_subset hsub ?_
    filter_upwards [ae_restrict_of_ae (ae_restrict_mem hT),
      ae_restrict_mem (hW.measurableSet.union hT.compl)] with a haT haW
    rcases haW with haW | haT'
    · rw [hloc j a haW]
    · exact absurd haT haT'
  · rfl

end

end ReciprocityTheory.AnForm.P
