import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ChainLog

theorem loc_fn_eventuallyEq {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (u : M → ℝ) (x : A.Pt) :
    A.loc (A.fn u) x.1.1 =ᶠ[𝓝 x.crd] fun v => algebraMap ℂ (Alt n) ((u ((A.e x.1.1).symm v) : ℝ) : ℂ) := by
  filter_upwards [(A.e x.1.1).open_target.mem_nhds ((A.e x.1.1).map_source x.2)] with v hv
  rw [HolAtlas.loc, dif_pos hv]
  rfl

theorem delAt_fun {n : ℕ} (g : V n → ℂ) (v : V n) :
    delAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ a, GlobalTheory.del g v (GlobalTheory.GoodMetric.coordVec a) • dz a := by
  simp only [delAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dbarAt_fun {n : ℕ} (g : V n → ℂ) (v : V n) :
    dbarAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ b, GlobalTheory.dbar g v (GlobalTheory.GoodMetric.coordVec b) • dzb b := by
  simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

end GlobalTheory.ChainLog

namespace GlobalTheory.ChainLog

theorem ddc_fn_log_add : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ), A.SmoothOn Set.univ (fun y => (f y : ℂ)) → (∀ y, 0 ≤ f y) →
    ∀ t : ℝ, 0 < t → A.ddc (A.fn (fun y => Real.log (f y + t))) =
      A.fn (fun y => 1 / (f y + t)) * A.ddc (A.fn f) - A.fn (fun y => 1 / (f y + t) ^ 2) * (GlobalTheory.HermFrame.kappa • (A.del (A.fn f) * A.dbar (A.fn f))) := by
  intro M _ n A f hf hf0 t ht
  funext x
  set e := A.e x.1.1 with he
  set v0 := x.crd with hv0
  set w : V n → ℝ := fun v => f (e.symm v) with hwdef
  have hpt : e.symm v0 = x.pt := e.left_inv x.2
  have hw0 : w v0 = f x.pt := by simp only [hwdef, hpt]
  have hnhds : e.target ∈ 𝓝 v0 := e.open_target.mem_nhds (e.map_source x.2)
  have hwS : ContDiffAt ℝ ∞ w v0 := by
    have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf x.1.1)
    have h2 : ContDiffOn ℝ ∞ w e.target :=
      (h1.mono fun v hv => ⟨hv, trivial⟩).congr fun v _ => by simp [hwdef, he]
    exact h2.contDiffAt hnhds
  have hw : ContDiffAt ℝ 2 w v0 := hwS.of_le (WithTop.coe_le_coe.2 le_top)
  have hne : w v0 + t ≠ 0 := by rw [hw0]; linarith [hf0 x.pt]
  have hh : ContDiffAt ℝ 2 (fun s : ℝ => Real.log (s + t)) (w v0) :=
    (contDiffAt_id.add contDiffAt_const).log hne
  have hlw : ContDiffAt ℝ 2 (fun v => Real.log (w v + t)) v0 := hh.comp v0 hw
  have hL : ∀ p q, GlobalTheory.leviForm (fun v => Real.log (w v + t)) v0 p q =
      ((deriv (fun s : ℝ => Real.log (s + t)) (w v0) : ℝ) : ℂ) * GlobalTheory.leviForm w v0 p q
        + ((deriv (deriv (fun s : ℝ => Real.log (s + t))) (w v0) : ℝ) : ℂ) *
          (GlobalTheory.del (fun v => (w v : ℂ)) v0 p * GlobalTheory.dbar (fun v => (w v : ℂ)) v0 q) :=
    fun p q => GlobalTheory.leviForm_real_comp hh hw p q
  rw [GlobalTheory.deriv_deriv_log_add_const, GlobalTheory.deriv_log_add_const] at hL
  have hddc : ∀ u : M → ℝ, A.ddc (A.fn u) x = GlobalTheory.HermFrame.kappa • delAt (dbarAt fun v => algebraMap ℂ (Alt n) ((u (e.symm v) : ℝ) : ℂ)) v0 :=
    fun u => GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq A _ x _ (loc_fn_eventuallyEq A u x)
  have hdel : A.del (A.fn f) x = ∑ a, GlobalTheory.del (fun v => (w v : ℂ)) v0 (GlobalTheory.GoodMetric.coordVec a) • dz a := by
    change delAt (A.loc (A.fn f) x.1.1) x.crd = _
    rw [GlobalTheory.SecForm.DdcGerm.delAt_germ (loc_fn_eventuallyEq A f x), delAt_fun]
  have hdbar : A.dbar (A.fn f) x = ∑ b, GlobalTheory.dbar (fun v => (w v : ℂ)) v0 (GlobalTheory.GoodMetric.coordVec b) • dzb b := by
    change dbarAt (A.loc (A.fn f) x.1.1) x.crd = _
    rw [GlobalTheory.SecForm.DdcGerm.dbarAt_germ (loc_fn_eventuallyEq A f x), dbarAt_fun]
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply]
  rw [hddc, hddc, hdel, hdbar]
  rw [show (fun v => algebraMap ℂ (Alt n) (((fun y => Real.log (f y + t)) (e.symm v) : ℝ) : ℂ))
      = fun v => algebraMap ℂ (Alt n) ((Real.log (w v + t) : ℝ) : ℂ) from rfl,
    delAt_dbarAt_fun hlw, show (fun v => algebraMap ℂ (Alt n) ((f (e.symm v) : ℝ) : ℂ))
      = fun v => algebraMap ℂ (Alt n) ((w v : ℝ) : ℂ) from rfl, delAt_dbarAt_fun hw]
  simp only [HolAtlas.fn, ← hpt, ← Algebra.smul_def, ofValues, GlobalTheory.HermFrame.ddc, hL, AddSubmonoidClass.coe_finset_sum,
    Subalgebra.coe_smul, sym, Finset.sum_mul_sum, smul_mul_smul_comm, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib,
    ← sub_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp only [hwdef]
  push_cast
  ring

end GlobalTheory.ChainLog
