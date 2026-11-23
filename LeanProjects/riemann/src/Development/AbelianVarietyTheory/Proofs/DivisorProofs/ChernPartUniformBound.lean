import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.MetFam

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb)
open scoped ContDiff ENNReal

theorem contDiffAt_fderiv_snd {D : ℕ} {Θ : ℝ × V D → ℂ} {x₀ : ℝ × V D} {m n : WithTop ℕ∞} (h : ContDiffAt ℝ n Θ x₀)
    (hmn : m + 1 ≤ n) (e : V D) :
    ContDiffAt ℝ m (fun x : ℝ × V D => fderiv ℝ (fun v => Θ (x.1, v)) x.2 e) x₀ := by
  have h₁ : ContDiffAt ℝ n (Function.uncurry fun (x : ℝ × V D) (v : V D) => Θ (x.1, v)) (x₀, x₀.2) :=
    ContDiffAt.comp (g := Θ) (f := fun w : (ℝ × V D) × V D => (w.1.1, w.2)) (x₀, x₀.2) h
      ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
  exact (h₁.fderiv contDiffAt_snd hmn).clm_apply contDiffAt_const

theorem continuousAt_cHess_snd {D : ℕ} {Θ : ℝ × V D → ℂ} {x₀ : ℝ × V D} (h : ContDiffAt ℝ 2 Θ x₀) :
    ContinuousAt (fun x : ℝ × V D => cHess D (fun v => Θ (x.1, v)) x.2) x₀ := by
  refine continuousAt_pi.2 fun j => continuousAt_pi.2 fun l => ?_
  have h₁ : ContDiffAt ℝ 1 (fun x : ℝ × V D => wdb D l (fun v => Θ (x.1, v)) x.2) x₀ :=
    ((contDiffAt_fderiv_snd h (by norm_num) _).add
      (contDiffAt_const.mul (contDiffAt_fderiv_snd h (by norm_num) _))).div_const 2
  have h₂ : ContDiffAt ℝ 0 (fun x : ℝ × V D =>
      wd D j (fun v => wdb D l (fun w => Θ (x.1, w)) v) x.2) x₀ :=
    ((contDiffAt_fderiv_snd h₁ (by norm_num) _).sub
      (contDiffAt_const.mul (contDiffAt_fderiv_snd h₁ (by norm_num) _))).div_const 2
  exact h₂.continuousAt

theorem FamAt.exists_bound_chernDens {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {t : ℝ → ℝ} (ht : Tendsto t atTop (𝓝 0)) {B : LB X} {φ : Weight p σ B} (hφ : φ.IsCInf)
    {u : ℝ → CxPts p σ → ℝ} (hu : ∀ R y, CInfAt (u R) y) {u₀ : CxPts p σ → ℝ} {y : CxPts p σ} (h : FamAt t u u₀ y)
    (c : AlgChart p σ D) (hy : y ∈ c.e.source) :
    ∃ K : ℝ, ∀ᶠ x : ℝ × CxPts p σ in atTop ×ˢ 𝓝 y, |c.chernDens (φ.addFn (u x.1)) x.2| ≤ K := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, -, h₆⟩ := h
  have hi := mem_pick φ.isLB y
  set i := pick φ.isLB y
  set Θ : ℝ × V D → ℂ := fun x => ((φ.φ i (c.e.symm x.2) + Φ (x.1, f (c.e.symm x.2)) : ℝ) : ℂ) with hΘ
  have hΘd : ContDiffAt ℝ 2 Θ (0, c.e y) := by
    have a₁ : ContDiffAt ℝ 2 (fun x : ℝ × V D => φ.φ i (c.e.symm x.2)) (0, c.e y) :=
      ContDiffAt.comp (g := fun v => φ.φ i (c.e.symm v)) (0, c.e y) (hφ.contDiffAt c hy hi) contDiffAt_snd
    have a₂ : ContDiffAt ℝ 2 (fun x : ℝ × V D => f (c.e.symm x.2)) (0, c.e y) :=
      ContDiffAt.comp (g := fun v => f (c.e.symm v)) (0, c.e y)
        ((h₁.contDiffAt_chart c hy).of_le (by norm_cast)) contDiffAt_snd
    have a₃ : ContDiffAt ℝ 2 Φ (0, f (c.e.symm (c.e y))) := by
      rw [c.e.left_inv hy]
      exact (h₄.contDiffAt (h₂.mem_nhds h₃)).of_le (by norm_cast)
    have a₄ : ContDiffAt ℝ 2 (fun x : ℝ × V D => Φ (x.1, f (c.e.symm x.2))) (0, c.e y) :=
      ContDiffAt.comp (g := Φ) (f := fun x : ℝ × V D => (x.1, f (c.e.symm x.2))) (0, c.e y) a₃
        (contDiffAt_fst.prodMk a₂)
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (a₁.add a₄)
  set G : ℝ × V D → ℝ := fun x => D.factorial / Real.pi ^ D * (cHess D (fun v => Θ (x.1, v)) x.2).det.re with hG
  have hGc : ContinuousAt G (0, c.e y) :=
    continuousAt_const.mul (Complex.continuous_re.continuousAt.comp
      ((continuous_id.matrix_det).continuousAt.comp (continuousAt_cHess_snd hΘd)))
  have hT : Tendsto (fun x : ℝ × CxPts p σ => G (t x.1, c.e x.2)) (atTop ×ˢ 𝓝 y) (𝓝 (G (0, c.e y))) :=
    hGc.tendsto.comp ((ht.comp tendsto_fst).prodMk_nhds ((c.e.continuousAt hy).tendsto.comp tendsto_snd))
  refine ⟨|G (0, c.e y)| + 1, ?_⟩
  obtain ⟨pa, ha, pb, hb, hab⟩ := eventually_prod_iff.1 h₆
  filter_upwards [hT.abs.eventually (ge_mem_nhds (lt_add_one _)), tendsto_fst.eventually ha,
    tendsto_snd.eventually hb.eventually_nhds, tendsto_snd.eventually (c.e.open_source.mem_nhds hy),
    tendsto_snd.eventually ((isOpen_ptsIn (B.U i)).mem_nhds hi)] with x hx hxa hxb hxs hxi
  have e : (fun v => ((φ.addFn (u x.1)).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e x.2)] fun v => Θ (t x.1, v) := by
    have hc := c.e.continuousAt_symm (c.e.map_source hxs)
    rw [ContinuousAt, c.e.left_inv hxs] at hc
    filter_upwards [hc.eventually hxb] with v hv
    simp only [hΘ, Weight.addFn, hab hxa hv]
  rw [c.chernDens_eq (hφ.addFn (hu x.1)) hxs hxi, AlgChart.hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]
  exact hx

theorem exists_bound_chernPart_univ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (σ : k →+* ℂ) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ u : ℝ → CxPts p σ → ℝ, (∀ R y, CInfAt (u R) y) → (∀ y, FamAt t u (fun _ => 0) y) → ∃ C : NNReal, ∀ᶠ R in atTop, ∀ ε : ℤˣ, (φ.addFn (u R)).chernPart D ε Set.univ ≤ (C : ENNReal) := by
  intro k _ X _ p D hX hS t ht σ B φ hφ u hu hF
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨A⟩ := hS σ
  have hloc : ∀ y : CxPts p σ, ∃ U : Set (CxPts p σ), IsOpen U ∧ y ∈ U ∧ ∃ C : NNReal,
      ∀ᶠ R in atTop, ∀ ε : ℤˣ, (φ.addFn (u R)).chernPart D ε U ≤ (C : ENNReal) := by
    intro y
    obtain ⟨a, hy⟩ := A.cover y
    set c := A.chart a
    obtain ⟨K, hK⟩ := (hF y).exists_bound_chernDens ht hφ hu c hy
    obtain ⟨pa, ha, pb, hb, hab⟩ := eventually_prod_iff.1 hK
    have hball : ∀ᶠ z in 𝓝 y, c.e z ∈ Metric.closedBall (c.e y) 1 :=
      (c.e.continuousAt hy).eventually (Metric.closedBall_mem_nhds _ one_pos)
    obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1 (hb.and (hball.and (c.e.open_source.mem_nhds hy)))
    have hUs : U ⊆ c.e.source := fun z hz => (hU z hz).2.2
    have hfin : ENNReal.ofReal K * volume (Metric.closedBall (c.e y) 1) ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top).ne
    refine ⟨U, hUo, hyU, (ENNReal.ofReal K * volume (Metric.closedBall (c.e y) 1)).toNNReal, ?_⟩
    filter_upwards [ha] with R hR ε
    rw [ENNReal.coe_toNNReal hfin, Weight.chernPart_apply (hφ.addFn (hu R)) ε c hUo.measurableSet hUs]
    have hm := GlobalTheory.ChartGlue.measurableSet_image c.e hUo.measurableSet hUs
    calc _ ≤ ∫⁻ _ in c.e '' U, ENNReal.ofReal K := by
          refine setLIntegral_mono' hm ?_
          rintro _ ⟨z, hz, rfl⟩
          refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
          rw [c.e.left_inv (hUs hz), abs_mul]
          have := hab hR (hU z hz).1
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simpa using this
      _ = ENNReal.ofReal K * volume (c.e '' U) := setLIntegral_const _ _
      _ ≤ _ := by
          gcongr
          rintro _ ⟨z, hz, rfl⟩
          exact (hU z hz).2.1
  choose U hUo hyU C hC using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUo (fun y _ => Set.mem_iUnion.2 ⟨y, hyU y⟩)
  refine ⟨∑ y ∈ s, C y, ?_⟩
  filter_upwards [(eventually_all_finset s).2 fun y _ => hC y] with R hR ε
  refine (measure_mono hs).trans ((measure_biUnion_finset_le s U).trans ?_)
  rw [ENNReal.coe_finset_sum]
  exact Finset.sum_le_sum fun y hy => hR y hy ε

end GlobalTheory.MetFam
