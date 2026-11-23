import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets

namespace RatSheetSumMeasurable

variable {n d : ℕ}

theorem continuousOn_ratMap (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {z | eval z q ≠ 0} := by
  show ContinuousOn (fun z r => eval z (p r) / eval z q) _
  exact continuousOn_pi.2 fun r => (MvPolynomial.continuous_eval (p r)).continuousOn.div
    (MvPolynomial.continuous_eval q).continuousOn fun z hz => hz

theorem sheet_eventuallyEq {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ} {s s' : (Fin d → ℂ) → Fin n → ℂ}
    (hs : RatChart.IsRatSheetAt J p q x s) (hs' : RatChart.IsRatSheetAt J p q x s') :
    s' =ᶠ[𝓝 (RatChart.ratMap p q x)] s := by
  obtain ⟨U, hU, hxU, -, -, -, V, hV, hVs⟩ := hs
  obtain ⟨U', hU', hxU', hsd', hsx', hsec', -⟩ := hs'
  have hcont : ContinuousAt s' (RatChart.ratMap p q x) := hsd'.continuousOn.continuousAt (hU'.mem_nhds hxU')
  have h1 : ∀ᶠ w in 𝓝 (RatChart.ratMap p q x), s' w ∈ V :=
    hcont.preimage_mem_nhds (by rw [hsx']; exact hV)
  filter_upwards [h1, hU.mem_nhds hxU, hU'.mem_nhds hxU'] with w hwV hwU hwU'
  obtain ⟨hZ, hq, hR⟩ := hsec' w hwU'
  have h := hVs (s' w) ⟨hZ, hwV⟩ hq (by rw [hR]; exact hwU)
  rw [hR] at h
  exact h

theorem term_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    (h : ∃ s, RatChart.IsRatSheetAt J p q x s) :
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (RatChart.ratMap p q x)) =
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (RatChart.ratMap p q x)) := by
  rw [IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k =>
    ((sheet_eventuallyEq hs h.choose_spec).fun_comp (φ k))]

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ ContinuousOn s U ∧
      (∀ y ∈ U, s y ∈ zeroSet J ∧ eval (s y) q ≠ 0 ∧ RatChart.ratMap p q (s y) = y) ∧
      (∀ x' ∈ zeroSet J ∩ W, RatChart.ratMap p q x' ∈ U ∧ RatChart.IsRatSheetAt J p q x' s) ∧
      ((∃ s, RatChart.IsRatSheetAt J p q x s) → x ∈ W) := by
  by_cases hx : ∃ s, RatChart.IsRatSheetAt J p q x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hQ : IsOpen {z : Fin n → ℂ | eval z q ≠ 0} :=
      isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const
    have hxq : eval x q ≠ 0 := by
      have := (hsec _ hxU).2.1
      rwa [hsx] at this
    refine ⟨s, U, ({z | eval z q ≠ 0} ∩ RatChart.ratMap p q ⁻¹' U) ∩ interior V, hU,
      ((continuousOn_ratMap p q).isOpen_inter_preimage hQ hU).inter isOpen_interior,
      hsd.continuousOn, hsec, ?_, fun _ => ⟨⟨hxq, hxU⟩, mem_interior_iff_mem_nhds.2 hV⟩⟩
    rintro x' ⟨hx'Z, ⟨hx'q, hx'U⟩, hx'V⟩
    have hx's : s (RatChart.ratMap p q x') = x' :=
      (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'q hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hq'' hU'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hq'' hU''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, continuousOn_empty _, by simp,
      by simp, fun h => absurd h hx⟩

end RatSheetSumMeasurable

open Classical in

theorem RatSheetSumMeasurable.proof : RatSheetSumMeasurable.Statement := by
  intro n d J p q Φ g φ hfin0 hΦ hg
  open RatSheetSumMeasurable in
  choose σ U W hU hW hσc hσsec hWsh hxW using
    fun x : Fin n → ℂ => exists_sheet_nhds (J := J) (p := p) (q := q) x

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : ∀ x, (∃ s, RatChart.IsRatSheetAt J p q x s) → ∃ k, x ∈ W (e k) := by
    intro x hx
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hx⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact ⟨k, hxi⟩

  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hW (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ zeroSet J ∩ W (e k) := fun k x hx =>
    ⟨hx.1, disjointed_subset (fun k => W (e k)) k hx.2⟩
  have hEdisj : ∀ k k' x, x ∈ E k → x ∈ E k' → k = k' := by
    intro k k' x hk hk'
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_disjointed (fun k => W (e k)) hne) hk.2 hk'.2
  have hEcover : ∀ x, (∃ s, RatChart.IsRatSheetAt J p q x s) → ∃ k, x ∈ E k := by
    intro x hx
    obtain ⟨m, hm⟩ := hcover x hx
    have hxZ : x ∈ zeroSet J := by
      obtain ⟨s, U₀, -, hxU₀, -, hsx, hsec, -⟩ := hx
      rw [← hsx]
      exact (hsec _ hxU₀).1
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  set t : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, RatChart.IsRatSheetAt J p q x s then
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (RatChart.ratMap p q x)) else 0 with ht
  have htdef : ∀ x, t x = if h : ∃ s, RatChart.IsRatSheetAt J p q x s then
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (RatChart.ratMap p q x)) else 0 :=
    fun x => rfl
  have htE : ∀ k x, x ∈ E k →
      t x = Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k' => φ k' ∘ σ (e k)) (RatChart.ratMap p q x)) := by
    intro k x hx
    have hsh := (hWsh (e k) x (hEW k hx)).2
    rw [htdef, dif_pos ⟨_, hsh⟩]
    exact RatSheetSumMeasurable.term_eq Φ g φ hsh _

  set σ' : ℕ → (Fin d → ℂ) → Fin n → ℂ := fun k => (U (e k)).piecewise (σ (e k)) fun _ => 0
    with hσ'
  set f : ℕ → (Fin d → ℂ) → ℝ := fun k => (U (e k) ∩ σ' k ⁻¹' E k).indicator
    (fun y => Φ (g (σ' k y)) (ReciprocityTheory.AnForm.maDens (fun k' => φ k' ∘ σ (e k)) y)) with hf
  have hσ'm : ∀ k, Measurable (σ' k) := fun k =>
    (hσc (e k)).measurable_piecewise continuousOn_const (hU (e k)).measurableSet
  have hfm : ∀ k, Measurable (f k) := fun k =>
    (hΦ.comp ((hg.comp (hσ'm k)).prodMk (SheetSumMeasurable.measurable_maDens _))).indicator
      ((hU (e k)).measurableSet.inter (hσ'm k (hEm k)))

  have hpiece : ∀ (k : ℕ) (y : Fin d → ℂ) (F : Finset (Fin n → ℂ)),
      (∀ x, x ∈ F ↔ x ∈ RatChart.ratFibre J p q y) → ∑ x ∈ F, (E k).indicator t x = f k y := by
    intro k y F hF
    by_cases hy : y ∈ U (e k) ∧ σ (e k) y ∈ E k
    · have hσ'y : σ' k y = σ (e k) y := by simp [hσ', Set.piecewise_eq_of_mem _ _ _ hy.1]
      have hx0 : σ (e k) y ∈ F :=
        (hF _).2 ⟨(hEW k hy.2).1, (hσsec (e k) y hy.1).2.1, (hσsec (e k) y hy.1).2.2⟩
      rw [Finset.sum_eq_single_of_mem _ hx0, Set.indicator_of_mem hy.2, htE k _ hy.2,
        (hσsec (e k) y hy.1).2.2, hf]
      · simp only
        rw [Set.indicator_of_mem (show y ∈ U (e k) ∩ σ' k ⁻¹' E k from
          ⟨hy.1, by simp only [Set.mem_preimage, hσ'y]; exact hy.2⟩), hσ'y]
      · intro x hxF hne
        refine Set.indicator_of_notMem (fun hxE => hne ?_) _
        obtain ⟨-, -, hRx⟩ := (hF x).1 hxF
        obtain ⟨-, hsh⟩ := hWsh (e k) x (hEW k hxE)
        obtain ⟨-, -, -, -, hsx, -⟩ := hsh
        rw [← hsx, hRx]
    · have hfy : f k y = 0 := by
        rw [hf]
        refine Set.indicator_of_notMem (fun hmem => hy ⟨hmem.1, ?_⟩) _
        have hσ'y : σ' k y = σ (e k) y := by simp [hσ', Set.piecewise_eq_of_mem _ _ _ hmem.1]
        have := hmem.2
        simp only [Set.mem_preimage, hσ'y] at this
        exact this
      rw [hfy]
      refine Finset.sum_eq_zero fun x hxF => Set.indicator_of_notMem (fun hxE => hy ?_) _
      obtain ⟨-, -, hRx⟩ := (hF x).1 hxF
      obtain ⟨hRU, hsh⟩ := hWsh (e k) x (hEW k hxE)
      obtain ⟨-, -, -, -, hsx, -⟩ := hsh
      rw [hRx] at hRU hsx
      exact ⟨hRU, hsx ▸ hxE⟩

  refine measurable_of_tendsto_metrizable (f := fun N y => ∑ k ∈ Finset.range N, f k y)
    (fun N => Finset.measurable_sum _ fun k _ => hfm k) (tendsto_pi_nhds.2 fun y => ?_)
  have hfin := hfin0 y
  have hsum : RatChart.ratSheetSum J p q
      (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y =
      ∑ x ∈ hfin.toFinset, t x := by
    unfold RatChart.ratSheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    rw [htdef, hx.2.2]
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ x ∈ hfin.toFinset, ∀ᶠ N in atTop,
      t x = ∑ k ∈ Finset.range N, (E k).indicator t x := by
    intro x _
    by_cases hx : ∃ s, RatChart.IsRatSheetAt J p q x s
    · obtain ⟨k0, hk0⟩ := hEcover x hx
      filter_upwards [eventually_gt_atTop k0] with N hN
      rw [Finset.sum_eq_single_of_mem k0 (Finset.mem_range.2 hN), Set.indicator_of_mem hk0]
      intro k _ hk
      exact Set.indicator_of_notMem (fun hxk => hk (hEdisj k k0 x hxk hk0)) _
    · have htx : t x = 0 := by rw [htdef, dif_neg hx]
      refine Eventually.of_forall fun N => ?_
      rw [htx]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      by_cases hxk : x ∈ E k
      · rw [Set.indicator_of_mem hxk]; exact htx
      · exact Set.indicator_of_notMem hxk _
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => hpiece k y _ fun x => Set.Finite.mem_toFinset hfin

end GroundTheory.Heights₂.Heights
