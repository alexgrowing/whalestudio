import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContinuousTmaxShift
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

theorem closure_image_subset {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [T2Space Y] (e : OpenPartialHomeomorph X Y) {s : Set X} (hs : closure s ⊆ e.source) :
    IsCompact (e '' closure s) ∧ closure (e.target ∩ e.symm ⁻¹' s) ⊆ e '' closure s := by
  have hK : IsCompact (e '' closure s) :=
    isClosed_closure.isCompact.image_of_continuousOn (e.continuousOn.mono hs)
  refine ⟨hK, closure_minimal ?_ hK.isClosed⟩
  rintro y ⟨hy, hys⟩
  exact ⟨e.symm y, subset_closure hys, e.right_inv hy⟩

theorem closure_preimage_subset {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {s : Set Y} (hc : IsCompact (closure s))
    (hs : closure s ⊆ e.target) :
    closure (e.source ∩ e ⁻¹' s) ⊆ e.symm '' closure s := by
  have hK : IsCompact (e.symm '' closure s) := hc.image_of_continuousOn (e.continuousOn_symm.mono hs)
  refine closure_minimal ?_ hK.isClosed
  rintro x ⟨hx, hxs⟩
  exact ⟨e x, subset_closure hxs, e.left_inv hx⟩

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

namespace RegCharts

def ofPotentialCharts [CompactSpace X] (P : PotentialCharts A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) : RegCharts A where
  n := P.N
  ψ := P.chart
  compat := P.compat
  W j := (P.chart j).target
  W' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
  W'' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.inner j
  isOpen_kappaOpenNeighbourhood j := (P.chart j).open_target
  isOpen_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_mid j)
  isOpen_alt_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_inner j)
  W_subset _ := subset_rfl
  isCompact_closure_middle j :=
    (closure_image_subset (P.chart j) (P.closure_mid j)).1.of_isClosed_subset isClosed_closure
      (closure_image_subset (P.chart j) (P.closure_mid j)).2
  closure_W'_subset j := (closure_image_subset (P.chart j) (P.closure_mid j)).2.trans
    (image_subset_iff.2 fun _ hx => (P.chart j).map_source (P.closure_mid j hx))
  closure_W''_subset j := by
    have hs := (P.closure_inner j).trans (P.mid_subset_source j)
    refine (closure_image_subset (P.chart j) hs).2.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(P.chart j).map_source (hs hx), ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.mid j
    rw [(P.chart j).left_inv (hs hx)]
    exact P.closure_inner j hx
  cover x := by
    obtain ⟨j, hj⟩ := P.cover x
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hj)
    refine ⟨j, hs, (P.chart j).map_source hs, ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.inner j
    rw [(P.chart j).left_inv hs]
    exact hj
  θ := P.th
  θ_pot := P.th_pot
  om := om
  om_pot := om_pot
  om_pos := om_pos
  q := P.q
  q_smooth := P.q_smooth
  q_θ j y hy _ := by
    obtain ⟨V, hV, hyV, G, hG, hq⟩ := P.q_th j y y ⟨P.th.mem_U y, hy⟩
    refine ⟨V, hV, hyV, fun x => -G x, fun k => (hG k).neg, fun x hx _ => ?_⟩
    have := hq x hx
    simp only [Complex.neg_re]
    linarith

variable [CompactSpace X] (P : PotentialCharts A) (om : LocPot X) (om_pot : IsPotential A om)
  (om_pos : IsPosPot A om)

theorem ofPotentialCharts_V' (j : Fin P.N) :
    (ofPotentialCharts P om om_pot om_pos).V' j = P.mid j := by
  ext x
  constructor
  · rintro ⟨hx, -, hm⟩
    have hm' : (P.chart j).symm (P.chart j x) ∈ P.mid j := hm
    rwa [(P.chart j).left_inv hx] at hm'
  · intro hx
    have hs := P.mid_subset_source j hx
    refine ⟨hs, (P.chart j).map_source hs, ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.mid j
    rwa [(P.chart j).left_inv hs]

theorem ofPotentialCharts_V'' (j : Fin P.N) :
    (ofPotentialCharts P om om_pot om_pos).V'' j = P.inner j := by
  ext x
  constructor
  · rintro ⟨hx, -, hm⟩
    have hm' : (P.chart j).symm (P.chart j x) ∈ P.inner j := hm
    rwa [(P.chart j).left_inv hx] at hm'
  · intro hx
    have hs := P.mid_subset_source j (P.inner_subset_mid j hx)
    refine ⟨hs, (P.chart j).map_source hs, ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.inner j
    rwa [(P.chart j).left_inv hs]

end RegCharts

namespace RegCharts

variable (R : RegCharts A)

def restrChart (j : Fin R.n) : OpenPartialHomeomorph X (Fin D → ℂ) :=
  ((R.ψ j).symm.restrOpen (R.W j) (R.isOpen_kappaOpenNeighbourhood j)).symm

theorem restrChart_target (j : Fin R.n) : (R.restrChart j).target = R.W j :=
  inter_eq_right.2 (R.W_subset j)

def toPotentialCharts [T2Space X] (hW : ∀ j, R.W j ⊆ ball 0 1) : PotentialCharts A where
  N := R.n
  chart := R.restrChart
  compat j k := ⟨(R.compat j k).1.mono fun _ hy => ⟨hy.1, hy.2.1⟩,
    (R.compat j k).2.mono fun _ hy => ⟨hy.1.1, hy.2⟩⟩
  target_subset j := fun _ hy => hW j hy.2
  mid := R.V'
  inner := R.V''
  isOpen_mid j := (R.ψ j).isOpen_inter_preimage (R.isOpen_alt j)
  isOpen_inner j := (R.ψ j).isOpen_inter_preimage (R.isOpen_alt_alt j)
  closure_inner j := by
    have h1 : closure (R.W'' j) ⊆ R.W' j := R.closure_W''_subset j
    have h2 : closure (R.W' j) ⊆ R.W j := R.closure_W'_subset j
    have hc : IsCompact (closure (R.W'' j)) := (R.isCompact_closure_middle j).of_isClosed_subset
      isClosed_closure (closure_minimal ((subset_closure.trans h1).trans subset_closure) isClosed_closure)
    have ht : closure (R.W'' j) ⊆ (R.ψ j).target :=
      h1.trans (subset_closure.trans (h2.trans (R.W_subset j)))
    refine (closure_preimage_subset (R.ψ j) hc ht).trans ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(R.ψ j).map_target (ht hy), ?_⟩
    show R.ψ j ((R.ψ j).symm y) ∈ R.W' j
    rw [(R.ψ j).right_inv (ht hy)]
    exact h1 hy
  closure_mid j := by
    have h2 : closure (R.W' j) ⊆ R.W j := R.closure_W'_subset j
    have ht : closure (R.W' j) ⊆ (R.ψ j).target := h2.trans (R.W_subset j)
    refine (closure_preimage_subset (R.ψ j) (R.isCompact_closure_middle j) ht).trans ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(R.ψ j).map_target (ht hy), ?_⟩
    show R.ψ j ((R.ψ j).symm y) ∈ R.W j
    rw [(R.ψ j).right_inv (ht hy)]
    exact h2 hy
  cover x := by
    obtain ⟨j, h1, h2⟩ := R.cover x
    exact ⟨j, h1, h2⟩
  th := R.θ
  th_pot := R.θ_pot
  q := R.q
  q_smooth j := (R.q_smooth j).mono inter_subset_right
  q_th j x y hy := by
    obtain ⟨hyx, hys, hyW⟩ := hy
    obtain ⟨V, hV, hyV, G₁, hG₁, h₁⟩ := R.q_θ j y hys hyW
    obtain ⟨V₂, hV₂, hyV₂, G₂, hG₂, h₂⟩ := R.θ_pot.2 x y y ⟨hyx, R.θ.mem_U y⟩
    refine ⟨V ∩ V₂ ∩ R.θ.U y, (hV.inter hV₂).inter (R.θ.isOpen_U y),
      ⟨⟨hyV, hyV₂⟩, R.θ.mem_U y⟩, fun z => -(G₁ z + G₂ z),
      fun k => (((hG₁ k).mono fun _ hz => ⟨hz.1, hz.2.1.1⟩).add
        ((hG₂ k).mono fun _ hz => ⟨hz.1, hz.2.1.2⟩)).neg, ?_⟩
    rintro z ⟨⟨⟨⟨hzV, hzV₂⟩, hzU⟩, hzx⟩, hzs, hzW⟩
    have e1 := h₁ z ⟨⟨hzV, hzU⟩, hzs⟩ hzW
    have e2 := h₂ z ⟨⟨hzV₂, hzx⟩, hzU⟩
    show R.q j (R.ψ j z) - R.θ.φ x z = (-(G₁ z + G₂ z)).re
    simp only [Complex.neg_re, Complex.add_re]
    linarith

variable [T2Space X] (hW : ∀ j, R.W j ⊆ ball 0 1)

end RegCharts

section RoundTrip

variable [CompactSpace X] [T2Space X]

end RoundTrip

theorem IsCutoffFamily.ofPotentialCharts [CompactSpace X] {P : PotentialCharts A} {om : LocPot X}
    {om_pot : IsPotential A om} {om_pos : IsPosPot A om} {η : Fin P.N → X → ℝ} {Cη : ℝ}
    (hη : P.IsCutoffFamily η Cη) (j : Fin P.N) :
    let R := RegCharts.ofPotentialCharts P om om_pot om_pos
    A.SmoothOn (R.V' j) (η j) ∧ (∀ x ∈ R.V' j, -1 ≤ η j x ∧ η j x ≤ 0) ∧
      (∀ x ∈ R.V'' j, η j x = 0) ∧
      ∃ K : Set (Fin D → ℂ), IsCompact K ∧ K ⊆ R.W' j ∧ ∀ x ∈ R.V' j, R.ψ j x ∉ K → η j x = -1 := by
  intro R
  have hV' : R.V' j = P.mid j := RegCharts.ofPotentialCharts_V' P om om_pot om_pos j
  have hV'' : R.V'' j = P.inner j := RegCharts.ofPotentialCharts_V'' P om om_pot om_pos j
  rw [hV', hV'']
  obtain ⟨L, hL, hLm, hLη⟩ := hη.eq_neg_one j
  have hLs : L ⊆ (P.chart j).source := hLm.trans (P.mid_subset_source j)
  refine ⟨hη.smooth j, hη.bounds j, hη.eq_zero j, P.chart j '' L,
    hL.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono hLs), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨(P.chart j).map_source (hLs hx), ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.mid j
    rw [(P.chart j).left_inv (hLs hx)]
    exact hLm hx
  · intro x hx hK
    exact hLη x ⟨hx, fun hxL => hK ⟨x, hxL, rfl⟩⟩

theorem IsCutoffFamily.toPotentialCharts [T2Space X] {R : RegCharts A} {hW : ∀ j, R.W j ⊆ ball 0 1}
    {C : ℝ} {η : Fin R.n → X → ℝ} (hη : R.IsCutoffFamily C η) (j : Fin R.n) :
    let P := R.toPotentialCharts hW
    A.SmoothOn (P.mid j) (η j) ∧ (∀ x ∈ P.mid j, -1 ≤ η j x ∧ η j x ≤ 0) ∧
      (∀ x ∈ P.inner j, η j x = 0) ∧
      ∃ L : Set X, IsClosed L ∧ L ⊆ P.mid j ∧ ∀ x ∈ P.mid j \ L, η j x = -1 := by
  intro P
  obtain ⟨h1, h2, h3, ⟨K, hK, hKW, hKη⟩, -⟩ := hη j
  have hKt : K ⊆ (R.ψ j).target := hKW.trans
    ((subset_closure.trans (R.closure_W'_subset j)).trans (R.W_subset j))
  refine ⟨h1, h2, h3, (R.ψ j).symm '' K,
    (hK.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono hKt)).isClosed, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨(R.ψ j).map_target (hKt hy), ?_⟩
    show R.ψ j ((R.ψ j).symm y) ∈ R.W' j
    rw [(R.ψ j).right_inv (hKt hy)]
    exact hKW hy
  · rintro x ⟨hx, hxL⟩
    refine hKη x hx fun hxK => hxL ⟨R.ψ j x, hxK, ?_⟩
    exact (R.ψ j).left_inv hx.1

theorem regMax_pad {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → Prop) [DecidablePred p]
    [Nonempty {j // p j}] (f : ι → ℝ) {c : ι} (hc : p c) {η : ℝ} (hη : 0 ≤ η) :
    regMax η (fun j => if p j then f j else f c - η) = regMax η (fun i : {j // p j} => f i) := by
  unfold regMax
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p
  have hmp : MeasurePreserving e (Measure.pi fun _ : ι => (volume : Measure ℝ))
      ((Measure.pi fun _ : {j // p j} => (volume : Measure ℝ)).prod
        (Measure.pi fun _ : {j // ¬p j} => (volume : Measure ℝ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℝ)) p
  set G : ({j // p j} → ℝ) → ℝ :=
    fun u => tmax (fun i : {j // p j} => f i + η * u i) * ∏ i, kθ (u i)
  set H : ({j // ¬p j} → ℝ) → ℝ := fun w => ∏ i, kθ (w i)
  have key : ∀ h : ι → ℝ,
      tmax (fun j => (if p j then f j else f c - η) + η * h j) * ∏ j, kθ (h j) =
        G (e h).1 * H (e h).2 := by
    intro h
    have hprod : ∏ j, kθ (h j) = (∏ i : {j // p j}, kθ (h i)) * ∏ i : {j // ¬p j}, kθ (h i) :=
      (Fintype.prod_subtype_mul_prod_subtype p (fun j => kθ (h j))).symm
    show _ = tmax (fun i : {j // p j} => f i + η * h i) * (∏ i : {j // p j}, kθ (h i)) *
      ∏ i : {j // ¬p j}, kθ (h i)
    rw [mul_assoc, ← hprod]
    by_cases h0 : ∏ j, kθ (h j) = 0
    · rw [h0, mul_zero, mul_zero]
    congr 1
    have hh : ∀ j, |h j| ≤ 1 / 2 := fun j =>
      abs_le_of_kθ_ne fun hj => h0 (Finset.prod_eq_zero (Finset.mem_univ j) hj)
    apply le_antisymm
    · apply tmax_le
      intro j
      by_cases hj : p j
      · rw [if_pos hj]
        exact le_tmax (fun i : {j // p j} => f i + η * h i) ⟨j, hj⟩
      · rw [if_neg hj]
        refine le_trans ?_ (le_tmax (fun i : {j // p j} => f i + η * h i) ⟨c, hc⟩)
        have h1 : η * h j ≤ η * (1 / 2) := mul_le_mul_of_nonneg_left (abs_le.1 (hh j)).2 hη
        have h2 : η * (-(1 / 2)) ≤ η * h c := mul_le_mul_of_nonneg_left (abs_le.1 (hh c)).1 hη
        show f c - η + η * h j ≤ f c + η * h c
        linarith
    · apply tmax_le
      intro i
      have := le_tmax (fun j => (if p j then f j else f c - η) + η * h j) i.1
      simp only [if_pos i.2] at this
      exact this
  simp_rw [key]
  rw [show (volume : Measure (ι → ℝ)) = Measure.pi fun _ => volume from rfl,
    hmp.integral_comp' (fun z => G z.1 * H z.2), integral_prod_mul]
  have hH : ∫ w, H w ∂(Measure.pi fun _ : {j // ¬p j} => (volume : Measure ℝ)) = 1 := by
    simp only [H]
    rw [integral_fintype_prod_eq_prod (fun _ => kθ)]
    simp [kθ_integral]
  rw [hH, mul_one]
  rfl

namespace PotentialCharts

variable (P : PotentialCharts A)

open Classical in

theorem glue_eq_pad (a : Fin P.N → X → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (x : X) {c : Fin P.N}
    (hc : x ∈ P.mid c) :
    P.glue a ε x = (haveI : Nonempty (Fin P.N) := ⟨c⟩
      regMax ε (fun j => if x ∈ P.mid j then a j x else a c x - ε)) + ε / 2 := by
  have : Nonempty (Fin P.N) := ⟨c⟩
  rw [PotentialCharts.glue, regMax_pad (fun j => x ∈ P.mid j) (fun j => a j x) hc hε]

end PotentialCharts

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
