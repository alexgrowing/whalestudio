import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAnResToAnalyticRes
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.EvalEqZeroOfAevalEqZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiSymMeasure
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.MemCoordIdealOfIsHomogeneous
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CNormSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeIntB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology
open scoped Manifold ContDiff ComplexConjugate

noncomputable section

namespace AnResToAnalyticRes

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]

theorem sameOrbit_iff {z z' : Ix κ → ℂ} :
    SameOrbit (ι := GlobalTheory κ) z z' ↔ ∃ c : ℂ, c ≠ 0 ∧ z = c • z' := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c (), hc (), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun _ => c, fun _ => hc, rfl⟩

theorem sameOrbit_symm {z z' : Ix κ → ℂ} (h : SameOrbit (ι := GlobalTheory κ) z z') :
    SameOrbit (ι := GlobalTheory κ) z' z := by
  obtain ⟨c, hc, rfl⟩ := sameOrbit_iff.1 h
  exact sameOrbit_iff.2 ⟨c⁻¹, inv_ne_zero hc, by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem sameOrbit_trans {a b c : Ix κ → ℂ} (h1 : SameOrbit (ι := GlobalTheory κ) a b)
    (h2 : SameOrbit (ι := GlobalTheory κ) b c) : SameOrbit (ι := GlobalTheory κ) a c := by
  obtain ⟨c1, hc1, rfl⟩ := sameOrbit_iff.1 h1
  obtain ⟨c2, hc2, rfl⟩ := sameOrbit_iff.1 h2
  exact sameOrbit_iff.2 ⟨c1 * c2, mul_ne_zero hc1 hc2, by rw [smul_smul]⟩

theorem blockNonzero_iff {z : Ix κ → ℂ} : (∀ k : Unit, ∃ i, z ⟨k, i⟩ ≠ 0) ↔ z ≠ 0 := by
  constructor
  · intro h h0
    obtain ⟨i, hi⟩ := h ()
    exact hi (congrFun h0 _)
  · intro hz k
    by_contra hk
    push Not at hk
    exact hz (funext fun p => hk p.2)

theorem mem_pts_iff {P : Ideal (MvPolynomial (Ix κ) ℤ)} {z : Ix κ → ℂ} :
    z ∈ pts P ↔ z ∈ mcPts (ι := GlobalTheory κ) P := by
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨blockNonzero_iff.2 hz, h⟩
  · rintro ⟨hz, h⟩
    exact ⟨blockNonzero_iff.1 hz, h⟩

theorem mem_mcPts_iff_gens {J : Ideal (MRing (GlobalTheory κ))} {r : ℕ} {g : Fin r → MRing (GlobalTheory κ)}
    (hg : J = Ideal.span (Set.range g)) {z : Ix κ → ℂ} (hz : z ≠ 0) :
    z ∈ mcPts (ι := GlobalTheory κ) J ↔ ∀ j, eval z (map (Int.castRingHom ℂ) (g j)) = 0 := by
  constructor
  · exact fun h j => h.2 _ (hg ▸ Ideal.subset_span ⟨j, rfl⟩)
  · intro h
    refine ⟨blockNonzero_iff.2 hz, fun f hf => ?_⟩
    have hle : J ≤ RingHom.ker ((eval z).comp (map (Int.castRingHom ℂ))) := by
      rw [hg, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact RingHom.mem_ker.2 (h j)
    exact RingHom.mem_ker.1 (hle hf)

theorem differentiable_evalPoly {I : Type} [Fintype I] (p : MvPolynomial I ℂ) :
    Differentiable ℂ fun z : I → ℂ => eval z p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (differentiable_apply i)

section Atlas

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isManifold_of_atlas [ChartedSpace (Fin e → ℂ) X] (A : FinHolAtlas e X)
    (hat : atlas (Fin e → ℂ) X = Set.range A.chart) : IsManifold 𝓘(ℂ, Fin e → ℂ) ∞ X := by
  apply isManifold_of_contDiffOn
  intro c c' hc hc'
  rw [hat] at hc hc'
  obtain ⟨j, rfl⟩ := hc
  obtain ⟨k, rfl⟩ := hc'
  have hs : ((A.chart j).symm ≫ₕ A.chart k).source =
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
    simp
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  have hc : ContDiffOn ℂ ∞ (A.chart k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
    (A.holo j k).contDiffOn ho.uniqueDiffOn
  simpa [hs] using hc

theorem mdifferentiableAt_of_chart [ChartedSpace (Fin e → ℂ) X] (A : FinHolAtlas e X)
    (hch : ∀ x, chartAt (Fin e → ℂ) x ∈ Set.range A.chart)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set X} {g : X → E}
    (hg : ∀ j, ∀ u ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U,
      DifferentiableAt ℂ (g ∘ (A.chart j).symm) u)
    {x : X} (hx : x ∈ U) : MDifferentiableAt 𝓘(ℂ, Fin e → ℂ) 𝓘(ℂ, E) g x := by
  obtain ⟨j, hj⟩ := hch x
  have hxs : x ∈ (A.chart j).source := by
    rw [hj]
    exact mem_chart_source (Fin e → ℂ) x
  have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hxs, by rw [Set.mem_preimage, (A.chart j).left_inv hxs]; exact hx⟩
  have hd := hg j _ hmem
  have hcont : ContinuousAt g x := by
    have h := hd.continuousAt.comp ((A.chart j).continuousAt hxs)
    refine h.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hxs] with y hy
    simp [(A.chart j).left_inv hy]
  rw [mdifferentiableAt_iff]
  refine ⟨hcont, ?_⟩
  rw [hj] at hd
  simpa [writtenInExtChartAt, extChartAt_model_space_eq_id, chartAt_self_eq] using hd.differentiableWithinAt

end Atlas

section Datum

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] (d : HSMDatum D Ω κ)

@[reducible] def cs : ChartedSpace (Fin D → ℂ) d.R.X := chartedSpaceOfAtlas d.R.A

attribute [local instance] cs

theorem isManifold : IsManifold 𝓘(ℂ, Fin D → ℂ) ∞ d.R.X :=
  isManifold_of_atlas d.R.A rfl

theorem lift_mdiff (x y : d.R.X) (hy : y ∈ d.R.U x) :
    MDifferentiableAt 𝓘(ℂ, Fin D → ℂ) 𝓘(ℂ, Ix κ → ℂ) (d.R.lift x) y := by
  refine mdifferentiableAt_of_chart d.R.A (fun _ => ⟨_, rfl⟩) (fun j u hu => ?_) hy
  rw [differentiableAt_pi]
  intro p
  exact (d.R.holo x p j u hu).differentiableAt

theorem nonempty_X : Nonempty d.R.X := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 : d.dV Set.univ = 1 := d.vol.1.measure_univ
  rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
  exact zero_ne_one h1

theorem exists_seq_cover : ∃ q : ℕ → d.R.X, ∀ y, ∃ n, y ∈ d.R.U (q n) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover d.R.U d.R.isOpen_U
    (fun y _ => Set.mem_iUnion.2 ⟨y, d.R.mem_U y⟩)
  have hne : (t : Set d.R.X).Nonempty := by
    obtain ⟨y⟩ := nonempty_X d
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨x, hx⟩
  obtain ⟨q, hq⟩ := t.countable_toSet.exists_eq_range hne
  refine ⟨q, fun y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  have hx' : x ∈ Set.range q := hq ▸ hx
  obtain ⟨n, rfl⟩ := hx'
  exact ⟨n, hy⟩

def seq : ℕ → d.R.X := (exists_seq_cover d).choose

theorem seq_cover (y : d.R.X) : ∃ n, y ∈ d.R.U (seq d n) := (exists_seq_cover d).choose_spec y

open Classical in

def idx (y : d.R.X) : ℕ := Nat.find (seq_cover d y)

def liftF (y : d.R.X) : Ix κ → ℂ := d.R.lift (seq d (idx d y)) y

theorem mem_U_idx (y : d.R.X) : y ∈ d.R.U (seq d (idx d y)) := by
  classical
  exact Nat.find_spec (seq_cover d y)

theorem liftF_orbit (y : d.R.X) : SameOrbit (ι := GlobalTheory κ) (liftF d y) (resPt d y) :=
  d.R.compat _ _ y ⟨mem_U_idx d y, d.R.mem_U y⟩

theorem liftF_eq_smul (y : d.R.X) : ∃ c : ℂ, c ≠ 0 ∧ liftF d y = c • resPt d y :=
  sameOrbit_iff.1 (liftF_orbit d y)

theorem liftF_mem (y : d.R.X) : liftF d y ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) :=
  d.R.mem _ y (mem_U_idx d y)

theorem measurable_liftF : Measurable (liftF d) := by
  classical
  have hg : ∀ n, Measurable ((d.R.U (seq d n)).piecewise (d.R.lift (seq d n)) 0) := fun n =>
    ContinuousOn.measurable_piecewise
      (fun y hy => (lift_mdiff d _ y hy).continuousAt.continuousWithinAt)
      continuousOn_const (d.R.isOpen_U _).measurableSet
  have h := Measurable.find (p := fun n y => y ∈ d.R.U (seq d n)) hg
    (fun n => (d.R.isOpen_U _).measurableSet) (seq_cover d)
  convert h using 1
  funext y
  simp only [liftF, idx]
  rw [Set.piecewise_eq_of_mem _ _ _ (Nat.find_spec (seq_cover d y))]

end Datum

section Res

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] (d : HSMDatum D Ω κ)

attribute [local instance] cs

theorem exists_gens : ∃ (r : ℕ) (g : Fin r → MRing (GlobalTheory κ)), d.J = Ideal.span (Set.range g) := by
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian d.J)
  exact ⟨r, g, hg.symm⟩

theorem liftF_mem_J_iff {r : ℕ} {g : Fin r → MRing (GlobalTheory κ)} (hg : d.J = Ideal.span (Set.range g))
    (x q : d.R.X) (hq : q ∈ d.R.U x) :
    liftF d q ∈ mcPts (ι := GlobalTheory κ) d.J ↔
      ∀ j, eval (d.R.lift x q) (map (Int.castRingHom ℂ) (g j)) = 0 := by
  have ho : SameOrbit (ι := GlobalTheory κ) (liftF d q) (d.R.lift x q) :=
    d.R.compat _ _ q ⟨mem_U_idx d q, hq⟩
  have hne : d.R.lift x q ≠ 0 := (mem_pts_iff.2 (d.R.mem x q hq)).1
  rw [← mem_mcPts_iff_gens hg hne]
  exact ⟨mem_mcPts_of_sameOrbit d.R.homog (sameOrbit_symm ho), mem_mcPts_of_sameOrbit d.R.homog ho⟩

theorem evalLift_mdiff (x : d.R.X) (p : MRing (GlobalTheory κ)) (y : d.R.X) (hy : y ∈ d.R.U x) :
    MDifferentiableAt 𝓘(ℂ, Fin D → ℂ) 𝓘(ℂ, ℂ)
      (fun q => eval (d.R.lift x q) (map (Int.castRingHom ℂ) p)) y :=
  DifferentiableAt.comp_mdifferentiableAt (g := fun z : Ix κ → ℂ => eval z (map (Int.castRingHom ℂ) p))
    (differentiable_evalPoly _ _) (lift_mdiff d x y hy)

theorem isAnalyticSubset_A :
    IndefiniteRowSideFullHecke.HilbertSamuel.IsAnalyticSubset D {q : d.R.X | liftF d q ∈ mcPts (ι := GlobalTheory κ) d.J} := by
  obtain ⟨r, g, hg⟩ := exists_gens d
  set A := {q : d.R.X | liftF d q ∈ mcPts (ι := GlobalTheory κ) d.J}
  have hcont : ∀ x j, ContinuousOn (fun q => eval (d.R.lift x q) (map (Int.castRingHom ℂ) (g j))) (d.R.U x) :=
    fun x j y hy => (evalLift_mdiff d x (g j) y hy).continuousAt.continuousWithinAt
  refine ⟨?_, fun q => ⟨d.R.U q, (d.R.isOpen_U q).mem_nhds (d.R.mem_U q), r,
    fun j q' => eval (d.R.lift q q') (map (Int.castRingHom ℂ) (g j)),
    fun j y hy => (evalLift_mdiff d q (g j) y hy).mdifferentiableWithinAt, ?_⟩⟩
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro q hq
    refine ⟨⋃ j, d.R.U q ∩ (fun q' => eval (d.R.lift q q') (map (Int.castRingHom ℂ) (g j))) ⁻¹' {0}ᶜ,
      ?_, isOpen_iUnion fun j => (hcont q j).isOpen_inter_preimage (d.R.isOpen_U q) isOpen_compl_singleton, ?_⟩
    · intro q' hq'
      obtain ⟨j, hq'U, hj⟩ := Set.mem_iUnion.1 hq'
      exact fun hA => hj (((liftF_mem_J_iff d hg q q' hq'U).1 hA) j)
    · have : ¬ ∀ j, eval (d.R.lift q q) (map (Int.castRingHom ℂ) (g j)) = 0 :=
        fun h => hq ((liftF_mem_J_iff d hg q q (d.R.mem_U q)).2 h)
      push Not at this
      obtain ⟨j, hj⟩ := this
      exact Set.mem_iUnion.2 ⟨j, d.R.mem_U q, hj⟩
  · ext q'
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, A]
    constructor
    · rintro ⟨hA, hU⟩
      exact ⟨hU, (liftF_mem_J_iff d hg q q' hU).1 hA⟩
    · rintro ⟨hU, h⟩
      exact ⟨(liftF_mem_J_iff d hg q q' hU).2 h, hU⟩

theorem dense_compl_A : Dense {q : d.R.X | liftF d q ∈ mcPts (ι := GlobalTheory κ) d.J}ᶜ := by
  rw [dense_iff_inter_open]
  rintro W hW ⟨y, hy⟩
  by_contra hempty
  have hWA : ∀ w ∈ W, liftF d w ∈ mcPts (ι := GlobalTheory κ) d.J := fun w hw => by
    by_contra h
    exact hempty ⟨w, hw, h⟩
  obtain ⟨j, hj⟩ := d.R.A.cover y
  have hTo : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' W) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm hW
  have hTne : ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' W).Nonempty :=
    ⟨_, (d.R.A.chart j).map_source hj, by rw [Set.mem_preimage, (d.R.A.chart j).left_inv hj]; exact hy⟩
  have hpos := hTo.measure_pos volume hTne
  have hsub : (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' W ⊆
      (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' {x | d.R.lift x x ∈ mcPts d.J} := by
    rintro u ⟨hu, huW⟩
    exact ⟨hu, mem_mcPts_of_sameOrbit d.R.homog (sameOrbit_symm (liftF_orbit d _)) (hWA _ huW)⟩
  exact hpos.ne' (measure_mono_null hsub (d.R.null j))

theorem pts_subset_closure (hND : NonvanishingDense.Statement) :
    pts (coordIdeal ℤ d.x) ⊆
      closure (pts (coordIdeal ℤ d.x) \ (pts (coordIdeal ℤ d.x) ∩ mcPts (ι := GlobalTheory κ) d.J)) := by
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  intro z hz
  refine closure_mono ?_ (hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP (mem_pts_iff.1 hz))
  rintro w ⟨hw, hgw⟩
  exact ⟨mem_pts_iff.2 hw, fun h => hgw (h.2.2 g hgJ)⟩

theorem liftF_onto (hND : NonvanishingDense.Statement) (z : Ix κ → ℂ) (hz : z ∈ pts (coordIdeal ℤ d.x)) :
    ∃ q, ∃ c : ℂ, c ≠ 0 ∧ z = c • liftF d q := by
  have hcl := pts_subset_closure d hND hz
  obtain ⟨w, hwS, hwlim⟩ := mem_closure_iff_seq_limit.1 hcl
  have hsurj : ∀ n, ∃ x, SameOrbit (ι := GlobalTheory κ) (d.R.lift x x) (w n) := fun n =>
    d.R.surj (w n) (mem_pts_iff.1 (hwS n).1) (fun h => (hwS n).2 ⟨(hwS n).1, h⟩)
  choose xs hxs using hsurj
  have := dI_secondCountable d.R.A
  obtain ⟨a, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := xs) (fun n => Set.mem_univ _)
  set L := d.R.lift a
  have hLlim : Tendsto (fun n => L (xs (φ n))) atTop (𝓝 (L a)) :=
    (lift_mdiff d a a (d.R.mem_U a)).continuousAt.tendsto.comp hlim
  have hev : ∀ᶠ n in atTop, xs (φ n) ∈ d.R.U a := hlim ((d.R.isOpen_U a).mem_nhds (d.R.mem_U a))
  have horb : ∀ᶠ n in atTop, ∃ b : ℂ, b ≠ 0 ∧ L (xs (φ n)) = b • w (φ n) := by
    filter_upwards [hev] with n hn
    exact sameOrbit_iff.1 (sameOrbit_trans (d.R.compat a _ _ ⟨hn, d.R.mem_U _⟩) (hxs (φ n)))
  have hz0 : z ≠ 0 := hz.1
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz0
  replace hi : z i ≠ 0 := hi
  have hwφ : Tendsto (fun n => w (φ n)) atTop (𝓝 z) := hwlim.comp hφ.tendsto_atTop
  have hwi : Tendsto (fun n => w (φ n) i) atTop (𝓝 (z i)) :=
    ((continuous_apply i).tendsto z).comp hwφ
  have hwi0 : ∀ᶠ n in atTop, w (φ n) i ≠ 0 := hwi.eventually_ne hi
  have heq : (fun n => (L (xs (φ n)) i / w (φ n) i) • w (φ n)) =ᶠ[atTop] fun n => L (xs (φ n)) := by
    filter_upwards [horb, hwi0] with n hb hn
    obtain ⟨b, -, hb⟩ := hb
    rw [hb]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_assoc, div_self hn, mul_one]
  have hlim2 : Tendsto (fun n => (L (xs (φ n)) i / w (φ n) i) • w (φ n)) atTop (𝓝 ((L a i / z i) • z)) :=
    ((((continuous_apply i).tendsto _).comp hLlim).div hwi hi).smul hwφ
  have hLa : L a = (L a i / z i) • z := tendsto_nhds_unique hLlim (hlim2.congr' heq)
  have hLa0 : L a ≠ 0 := (mem_pts_iff.2 (d.R.mem a a (d.R.mem_U a))).1
  have hc0 : L a i / z i ≠ 0 := by
    intro h
    rw [h, zero_smul] at hLa
    exact hLa0 hLa
  obtain ⟨b, hb, hfb⟩ := liftF_eq_smul d a
  generalize L a i / z i = c0 at hLa hc0
  refine ⟨a, (b * c0)⁻¹, inv_ne_zero (mul_ne_zero hb hc0), ?_⟩
  rw [hfb, show resPt d a = L a from rfl, hLa, smul_smul, smul_smul, mul_assoc,
    inv_mul_cancel₀ (mul_ne_zero hb hc0), one_smul]

theorem isAnalyticRes (hND : NonvanishingDense.Statement) :
    IndefiniteRowSideFullHecke.HilbertSamuel.IsAnalyticRes (coordIdeal ℤ d.x) D (liftF d) where
  mem q := mem_pts_iff.2 (liftF_mem d q)
  meas := measurable_liftF d
  holo q := by
    classical
    have hc : ∀ q' ∈ d.R.U q, ∃ c : ℂ, c ≠ 0 ∧ d.R.lift q q' = c • liftF d q' := fun q' hq' =>
      sameOrbit_iff.1 (d.R.compat q _ q' ⟨hq', mem_U_idx d q'⟩)
    refine ⟨fun q' => if h : q' ∈ d.R.U q then (hc q' h).choose else 1, ?_, ?_⟩
    · filter_upwards [(d.R.isOpen_U q).mem_nhds (d.R.mem_U q)] with q' hq'
      rw [dif_pos hq']
      exact (hc q' hq').choose_spec.1
    · refine (lift_mdiff d q q (d.R.mem_U q)).congr_of_eventuallyEq ?_
      filter_upwards [(d.R.isOpen_U q).mem_nhds (d.R.mem_U q)] with q' hq'
      simp only [dif_pos hq']
      exact ((hc q' hq').choose_spec.2).symm
  onto := liftF_onto d hND
  exc := by
    obtain ⟨r, g, hg⟩ := exists_gens d
    refine ⟨{q | liftF d q ∈ mcPts (ι := GlobalTheory κ) d.J}, pts (coordIdeal ℤ d.x) ∩ mcPts (ι := GlobalTheory κ) d.J,
      isAnalyticSubset_A d, dense_compl_A d, ⟨Set.inter_subset_left, fun z hz c hc => ?_, fun z _ => ?_⟩,
      pts_subset_closure d hND, fun q hq h => hq h.2, fun q q' hq hq' c hc => ?_, fun z hz hzB => ?_⟩
    · exact ⟨smul_mem_pts_coord d.x hz.1 hc, mcPts_smul d.R.homog (fun _ => c) (fun _ => hc) hz.2⟩
    · refine ⟨Set.univ, Filter.univ_mem, r, fun j w => eval w (map (Int.castRingHom ℂ) (g j)),
        fun j => (differentiable_evalPoly _).differentiableOn, ?_⟩
      ext w
      simp only [Set.mem_inter_iff, Set.mem_univ, and_true, true_and, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hw, hJ⟩
        exact ⟨hw, (mem_mcPts_iff_gens hg hw.1).1 hJ⟩
      · rintro ⟨hw, h⟩
        exact ⟨hw, (mem_mcPts_iff_gens hg hw.1).2 h⟩
    ·
      have hq1 : d.R.lift q q ∉ mcPts (ι := GlobalTheory κ) d.J := fun h =>
        hq (mem_mcPts_of_sameOrbit d.R.homog (liftF_orbit d q) h)
      have hne : liftF d q' ≠ 0 := (mem_pts_iff.2 (liftF_mem d q')).1
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact hne hc
      have h1 : SameOrbit (ι := GlobalTheory κ) (d.R.lift q q) (d.R.lift q' q') :=
        sameOrbit_trans (sameOrbit_symm (liftF_orbit d q))
          (sameOrbit_trans (sameOrbit_symm (sameOrbit_iff.2 ⟨c, hc0, hc⟩)) (liftF_orbit d q'))
      exact (d.R.inj q q' hq1 h1).symm
    ·
      have hzJ : z ∉ mcPts (ι := GlobalTheory κ) d.J := fun h => hzB ⟨hz, h⟩
      obtain ⟨x, hx⟩ := d.R.surj z (mem_pts_iff.1 hz) hzJ
      have ho : SameOrbit (ι := GlobalTheory κ) z (liftF d x) :=
        sameOrbit_trans (sameOrbit_symm hx) (sameOrbit_symm (liftF_orbit d x))
      obtain ⟨c, hc, hzc⟩ := sameOrbit_iff.1 ho
      refine ⟨x, fun h => hzJ (mem_mcPts_of_sameOrbit d.R.homog ho h), c, hc, hzc⟩

end Res

section Integrals

theorem conjPt_smul (c : ℂ) (z : Ix κ → ℂ) : conjPt (c • z) = conj c • conjPt z := by
  funext i
  simp [conjPt]

theorem pairVal_smul (m : ConeMetric ℂ (Ix κ)) {n : ℕ} {b b' : MvPolynomial (Ix κ) ℚ}
    (hb : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (hb' : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b' = map (Int.castRingHom ℚ) f)
    {c : ℂ} (hc : c ≠ 0) (z : Ix κ → ℂ) : pairVal m n b b' (c • z) = pairVal m n b b' z := by
  unfold pairVal
  rw [ResChiSymMeasure.evalQ_smul hb, ResChiSymMeasure.evalQ_smul hb', m.smul, map_mul, map_pow]
  have hcn : (‖c‖ : ℂ) ≠ 0 := by simpa using hc
  have key : c ^ n * conj c ^ n = (‖c‖ : ℂ) ^ (2 * n) := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    ring
  rw [show (((‖c‖ * m.ρ z) ^ (2 * n) : ℝ) : ℂ) = (‖c‖ : ℂ) ^ (2 * n) * ((m.ρ z ^ (2 * n) : ℝ) : ℂ) by
      push_cast; ring,
    show c ^ n * eval z (map (algebraMap ℚ ℂ) b) * (conj c ^ n * conj (eval z (map (algebraMap ℚ ℂ) b'))) =
      (c ^ n * conj c ^ n) * (eval z (map (algebraMap ℚ ℂ) b) * conj (eval z (map (algebraMap ℚ ℂ) b'))) by
      ring,
    key, mul_div_mul_left _ _ (pow_ne_zero _ hcn)]

theorem ptNorm_smul (m : ConeMetric ℂ (Ix κ)) {n : ℕ} {g : MvPolynomial (Ix κ) ℤ} (hg : g.IsHomogeneous n)
    {c : ℂ} (hc : c ≠ 0) (z : Ix κ → ℂ) :
    ptNorm m (Int.castRingHom ℂ) n g (c • z) = ptNorm m (Int.castRingHom ℂ) n g z := by
  unfold ptNorm
  rw [ResChiSymMeasure.eval_smul_of_homog (hg.map _) c z, m.smul, norm_mul, norm_pow, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero _ (norm_ne_zero_iff.2 hc))]

theorem integral_symMeasure {M : Type} [MeasurableSpace M] (dV : Measure M) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {G : (Ix κ → ℂ) → E} (hG : StronglyMeasurable G) {f : M → Ix κ → ℂ}
    (hf : Measurable f)
    (hi : Integrable (fun y => G (f y)) dV ↔ Integrable (fun y => G (conjPt (f y))) dV) :
    ∫ z, G z ∂IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure f dV =
      (2⁻¹ : ℝ) • ((∫ y, G (f y) ∂dV) + ∫ y, G (conjPt (f y)) ∂dV) := by
  have hg : Measurable (conjPt ∘ f) := ResChiSymMeasure.measurable_conjPt.comp hf
  have iA : Integrable G (dV.map f) ↔ Integrable (fun y => G (f y)) dV :=
    integrable_map_measure hG.aestronglyMeasurable hf.aemeasurable
  have iB : Integrable G (dV.map (conjPt ∘ f)) ↔ Integrable (fun y => G (conjPt (f y))) dV :=
    integrable_map_measure hG.aestronglyMeasurable hg.aemeasurable
  unfold IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure
  rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  by_cases h : Integrable (fun y => G (f y)) dV
  · rw [integral_add_measure (iA.2 h) (iB.2 (hi.1 h)), integral_map hf.aemeasurable hG.aestronglyMeasurable,
      integral_map hg.aemeasurable hG.aestronglyMeasurable]
    rfl
  · have hn : ¬ Integrable G (dV.map f + dV.map (conjPt ∘ f)) := by
      rw [integrable_add_measure]
      exact fun h' => h (iA.1 h'.1)
    rw [integral_undef hn, integral_undef h, integral_undef (fun h' => h (hi.2 h')), add_zero, smul_zero]

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] (d : HSMDatum D Ω κ)

theorem chi_eq (n : ℕ) :
    chi d.x d.m (IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (liftF d) d.dV) n = resChi d n := by
  have : IsProbabilityMeasure d.dV := d.vol.1
  have hmult : ∀ w : NumberField.InfinitePlace ℚ, (w.mult : ℝ) = 1 := by
    intro w
    have h1 := NumberField.totalWeight_eq_sum_mult ℚ
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self, Fintype.sum_unique] at h1
    rw [Subsingleton.elim w default, ← h1, Nat.cast_one]
  have hemb : ∀ w : NumberField.InfinitePlace ℚ, w.embedding = algebraMap ℚ ℂ :=
    fun w => Subsingleton.elim _ _
  have hw : (Height.totalWeight ℚ : ℝ) = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self, Nat.cast_one]
  have hf := measurable_liftF d
  have hg : Measurable (conjPt ∘ liftF d) := ResChiSymMeasure.measurable_conjPt.comp hf
  unfold resChi chi
  by_cases h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2
  swap
  · rw [dif_neg h, dif_neg h]
  rw [dif_pos h, dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r, b⟩ := p
  have hp' : IsSecBasis d.x n b := hp
  have hG : resGram d n b = realGram (K := ℚ) (fun _ => d.m)
      (fun _ => IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (liftF d) d.dV) n b := by
    ext k l
    obtain ⟨hmeas, C, hC⟩ := ResChiSymMeasure.pairVal_bound d.smooth (hp'.1 k) (hp'.1 l)
    have hi : Integrable (fun y => pairVal d.m n (b k) (b l) (liftF d y)) d.dV ↔
        Integrable (fun y => pairVal d.m n (b k) (b l) (conjPt (liftF d y))) d.dV :=
      iff_of_true (Integrable.of_bound (hmeas.comp hf).aestronglyMeasurable C
          (Filter.Eventually.of_forall fun y => hC _))
        (Integrable.of_bound (hmeas.comp hg).aestronglyMeasurable C
          (Filter.Eventually.of_forall fun y => hC _))
    have e1 : ∀ y, pairVal d.m n (b k) (b l) (liftF d y) = pairVal d.m n (b k) (b l) (resPt d y) := by
      intro y
      obtain ⟨c, hc, hcy⟩ := liftF_eq_smul d y
      rw [hcy, pairVal_smul d.m (hp'.1 k) (hp'.1 l) hc]
    have e2 : ∀ y, pairVal d.m n (b k) (b l) (conjPt (liftF d y)) =
        pairVal d.m n (b k) (b l) (conjPt (resPt d y)) := by
      intro y
      obtain ⟨c, hc, hcy⟩ := liftF_eq_smul d y
      rw [hcy, conjPt_smul, pairVal_smul d.m (hp'.1 k) (hp'.1 l) (by simpa using hc)]
    simp only [realGram, hmult, hemb, one_mul, Fintype.sum_unique]
    change _ = (∫ z, pairVal d.m n (b k) (b l) z ∂IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (liftF d) d.dV).re
    rw [integral_symMeasure d.dV hmeas.stronglyMeasurable hf hi]
    simp only [e1, e2, resGram, Complex.real_smul, Complex.re_ofReal_mul, Complex.add_re]
    ring
  rw [hG]
  simp only [l2Degree, hw, div_one]
  ring

theorem symmetricMeasure_l2Norm_eq_resolutionL2 (n : ℕ) (g : MvPolynomial (Ix κ) ℤ) (hg : g.IsHomogeneous n) :
    l2Norm d.m (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (liftF d) d.dV) n g = resolutionSectionL2Norm d n g := by
  unfold l2Norm resolutionSectionL2Norm
  congr 1
  have hG : Measurable fun z => ptNorm d.m (Int.castRingHom ℂ) n g z ^ 2 :=
    (ResolutionL2SymmetricMeasure.measurable_ptNorm d.m d.smooth n g).pow_const 2
  have hc : ∀ w, ptNorm d.m (Int.castRingHom ℂ) n g (conjPt w) = ptNorm d.m (Int.castRingHom ℂ) n g w :=
    ResolutionL2SymmetricMeasure.ptNorm_conjPt d.conjInv n g
  have e1 : ∀ y, ptNorm d.m (Int.castRingHom ℂ) n g (liftF d y) = ptNorm d.m (Int.castRingHom ℂ) n g (resPt d y) := by
    intro y
    obtain ⟨c, hc0, hcy⟩ := liftF_eq_smul d y
    rw [hcy, ptNorm_smul d.m hg hc0]
  rw [integral_symMeasure d.dV hG.stronglyMeasurable (measurable_liftF d) (by simp only [hc])]
  simp only [hc, e1, smul_eq_mul]
  ring

end Integrals

end AnResToAnalyticRes

open AnResToAnalyticRes in

theorem AnResToAnalyticRes.proof (hND : NonvanishingDense.Statement) : AnResToAnalyticRes.Statement := by
  intro D Ω _ _ κ _ d
  exact ⟨d.R.X, inferInstance, inferInstance, inferInstance, chartedSpaceOfAtlas d.R.A, isManifold d,
    d.meas, d.borel, liftF d, d.dV, isAnalyticRes d hND, (IsSmoothVolume.equiv d.R.A d.dV).1 d.vol,
    chi_eq d, symmetricMeasure_l2Norm_eq_resolutionL2 d⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
