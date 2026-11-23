import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAnResNullForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set

noncomputable section

namespace AnResNullForm

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_trans_nf {a b c : (Σ k, ι k) → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  exact ⟨fun k => c1 k * c2 k, fun k => mul_ne_zero (hc1 k) (hc2 k), by funext q; simp [mul_assoc]⟩

theorem sameOrbit_symm_nf {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  simp [← mul_assoc, inv_mul_cancel₀ (hc q.1)]

theorem isClosed_blockProportional :
    IsClosed {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
  simp only [ofPred_forall]
  refine isClosed_iInter fun k => isClosed_iInter fun i => isClosed_iInter fun i' => isClosed_eq ?_ ?_ <;>
    fun_prop

theorem blockProportional_of_sameOrbit {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) :
    ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  intro k i i'
  ring

theorem sameOrbit_of_blockProportional {a b : (Σ k, ι k) → ℂ} (ha : ∀ k, ∃ i, a ⟨k, i⟩ ≠ 0)
    (hb : ∀ k, ∃ i, b ⟨k, i⟩ ≠ 0) (h : ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩) :
    SameOrbit a b := by
  choose p hp using hb
  refine ⟨fun k => a ⟨k, p k⟩ / b ⟨k, p k⟩, fun k => ?_, ?_⟩
  · intro h0
    obtain ⟨i, hi⟩ := ha k
    have h1 := h k i (p k)
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · rw [h0, zero_mul] at h1
      exact hi ((mul_eq_zero_iff_right (hp k)).1 h1)
    · exact hp k h0
  · funext ⟨k, i⟩
    show a ⟨k, i⟩ = a ⟨k, p k⟩ / b ⟨k, p k⟩ * b ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hp k)]
    exact h k i (p k)

theorem eval_eq_zero_iff_of_sameOrbit {G : MRing ι} {dG : K → ℕ} (hG : IsMultiHomog G dG)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    eval z (map (Int.castRingHom ℂ) G) = 0 ↔ eval z' (map (Int.castRingHom ℂ) G) = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_smul_of_isMultiHomog hG,
    mul_eq_zero_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))]

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem continuousAt_lift (R : AnRes P J e) (x y : R.X) (hy : y ∈ R.U x) : ContinuousAt (R.lift x) y := by
  obtain ⟨j, hj⟩ := R.A.cover y
  rw [continuousAt_pi]
  intro p
  have hya : R.A.chart j y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by simpa [(R.A.chart j).left_inv hj] using hy⟩
  have h1 : ContinuousAt ((fun y' => R.lift x y' p) ∘ (R.A.chart j).symm) (R.A.chart j y) :=
    (R.holo x p j _ hya).continuousAt
  have h2 := h1.comp ((R.A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(R.A.chart j).left_inv hy']

theorem isAnalyticSubset (R : AnRes P J e) {G : MRing ι} {dG : K → ℕ} (hG : IsMultiHomog G dG) :
    R.A.IsAnalyticSubset {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} := by
  intro x
  refine ⟨R.U x, R.isOpen_U x, R.mem_U x, 1, fun _ y => eval (R.lift x y) (map (Int.castRingHom ℂ) G),
    fun _ j y hy => ?_, ?_⟩
  · exact analyticAt_eval_comp (F := fun y' => R.lift x ((R.A.chart j).symm y')) (fun p => R.holo x p j y hy) G
  · ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hy⟩
      exact ⟨hy, fun _ => (eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).2 h0⟩
    · rintro ⟨hy, h0⟩
      exact ⟨(eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).1 (h0 0), hy⟩

theorem interior_eq_empty (hND : NonvanishingDense.Statement) (R : AnRes P J e) (hP : IsArithVar P (e + 1))
    {G : MRing ι} {dG : K → ℕ} (hG : IsMultiHomog G dG) (hGP : G ∉ P) :
    interior {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} = ∅ := by
  set S := {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} with hS
  by_contra hne
  obtain ⟨x0, hx0⟩ := nonempty_iff_ne_empty.2 hne

  obtain ⟨x, hxW, hxJ⟩ : ∃ x ∈ interior S, R.lift x x ∉ mcPts J := by
    by_contra! hall
    obtain ⟨j, hj⟩ := R.A.cover x0
    have hopen : IsOpen (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      ((R.A.chart j).isOpen_image_iff_of_subset_source inter_subset_right).2
        (isOpen_interior.inter (R.A.chart j).open_source)
    have hpos : 0 < volume (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      hopen.measure_pos volume ⟨R.A.chart j x0, x0, ⟨hx0, hj⟩, rfl⟩
    have hsub : R.A.chart j '' (interior S ∩ (R.A.chart j).source) ⊆
        (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J} := by
      rintro _ ⟨y, ⟨hyW, hys⟩, rfl⟩
      exact ⟨(R.A.chart j).map_source hys, by simpa [(R.A.chart j).left_inv hys] using hall y hyW⟩
    exact hpos.ne' (measure_mono_null hsub (R.null j))
  set z := R.lift x x with hzdef
  have hzP : z ∈ mcPts P := R.mem x x (R.mem_U x)

  set C := {z' : (Σ k, ι k) → ℂ | ∀ f ∈ J, eval z' (map (Int.castRingHom ℂ) f) = 0} with hC
  have hCc : IsClosed C := by
    simp only [hC, ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval _)
      continuous_const
  have hzC : z ∉ C := fun h => hxJ ⟨hzP.1, h⟩
  set T := {z' | z' ∈ mcPts P ∧ eval z' (map (Int.castRingHom ℂ) G) ≠ 0} ∩ Cᶜ with hT
  have hzT : z ∈ closure T := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨w, ⟨hwt, hwC⟩, hw⟩ :=
      mem_closure_iff_nhds.1 (hND K ι P (e + 1) G hP hGP hzP) (t ∩ Cᶜ)
        (inter_mem ht (hCc.isOpen_compl.mem_nhds hzC))
    exact ⟨w, hwt, hw, hwC⟩

  have hex : ∀ z', ∃ x', z' ∈ T → SameOrbit (R.lift x' x') z' := fun z' => by
    by_cases h : z' ∈ T
    · obtain ⟨x', hx'⟩ := R.surj z' h.1.1 (fun hJ => h.2 hJ.2)
      exact ⟨x', fun _ => hx'⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose xc hxc using hex
  have hxcW : ∀ z' ∈ T, xc z' ∉ interior S := fun z' hz' hW =>
    hz'.1.2 ((eval_eq_zero_iff_of_sameOrbit hG (hxc z' hz')).1 (show xc z' ∈ S from interior_subset hW))
  have : NeBot (𝓝[T] z) := mem_closure_iff_nhdsWithin_neBot.1 hzT
  obtain ⟨x', hx'⟩ := exists_clusterPt_of_compactSpace (map xc (𝓝[T] z))

  have hprop : (R.lift x' x', z) ∈ {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
    refine isClosed_blockProportional.closure_subset (mem_closure_iff_nhds.2 fun t ht => ?_)
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 ht
    have hU : R.U x' ∩ R.lift x' ⁻¹' u ∈ 𝓝 x' :=
      inter_mem ((R.isOpen_U x').mem_nhds (R.mem_U x')) (continuousAt_lift R x' x' (R.mem_U x') hu)
    have hV : xc '' (v ∩ T) ∈ map xc (𝓝[T] z) :=
      mem_map.2 (mem_of_superset (inter_mem_nhdsWithin T hv) fun z' hz' => ⟨z', ⟨hz'.2, hz'.1⟩, rfl⟩)
    obtain ⟨_, ⟨hyU, hyu⟩, z', ⟨hz'v, hz'T⟩, rfl⟩ := clusterPt_iff_nonempty.1 hx' hU hV
    refine ⟨(R.lift x' (xc z'), z'), huv ⟨hyu, hz'v⟩, ?_⟩
    exact blockProportional_of_sameOrbit
      (sameOrbit_trans_nf (R.compat x' (xc z') (xc z') ⟨hyU, R.mem_U _⟩) (hxc z' hz'T))
  have horb : SameOrbit (R.lift x' x') z :=
    sameOrbit_of_blockProportional (R.mem x' x' (R.mem_U x')).1 hzP.1 hprop
  have hxx' : x = x' := R.inj x x' hxJ (sameOrbit_symm_nf horb)
  subst hxx'
  obtain ⟨_, hyW, z', hz'T, rfl⟩ :=
    clusterPt_iff_nonempty.1 hx' (isOpen_interior.mem_nhds hxW)
      (mem_map.2 (mem_of_superset self_mem_nhdsWithin fun z' hz' => ⟨z', hz', rfl⟩) :
        xc '' T ∈ map xc (𝓝[T] z))
  exact hxcW z' hz'T hyW

end AnResNullForm

theorem AnResNullForm.proof (hND : NonvanishingDense.Statement) : AnResNullForm.Statement := by
  intro e K _ ι _ P J R G dG hP hG hGP j
  have h := analyticNull R.A _ (AnResNullForm.isAnalyticSubset R hG)
    (AnResNullForm.interior_eq_empty hND R hP hG hGP) j
  refine measure_mono_null ?_ h
  rintro a ⟨ha, haS⟩
  exact ⟨(R.A.chart j).symm a, ⟨haS, (R.A.chart j).map_target ha⟩, (R.A.chart j).right_inv ha⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
