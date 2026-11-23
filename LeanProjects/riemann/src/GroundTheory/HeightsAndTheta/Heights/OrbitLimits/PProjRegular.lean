import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeH
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace ProjRegular

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

theorem proj_segre_lift_eq {x y : R.X} (hy : y ∈ R.U x) :
    ∃ c : ℂ, c ≠ 0 ∧ Ψ (segre (R.lift y y)) = c • Ψ (segre (R.lift x y)) := by
  obtain ⟨c, hc, hz⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr (fun k _ => hc k), ?_⟩
  rw [← map_smul]
  congr 1
  funext i
  simp only [segre, Pi.smul_apply, smul_eq_mul, hz, Finset.prod_mul_distrib]

theorem projCoord_eq {x y : R.X} (hy : y ∈ R.U x) :
    projCoord R Ψ y = fun i => Ψ (segre (R.lift x y)) i.succ / Ψ (segre (R.lift x y)) 0 := by
  obtain ⟨c, hc, h⟩ := proj_segre_lift_eq Ψ hy
  funext i
  simp only [projCoord, h, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

theorem proj_ne_zero_iff {x y : R.X} (hy : y ∈ R.U x) :
    Ψ (segre (R.lift y y)) 0 ≠ 0 ↔ Ψ (segre (R.lift x y)) 0 ≠ 0 := by
  obtain ⟨c, hc, h⟩ := proj_segre_lift_eq Ψ hy
  simp [h, hc]

theorem lift_analyticAt {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) {j : Fin BV.n} (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ (fun u => R.lift x.1 ((BV.chart j).symm u).1) (BV.chart j x) ∧
      ∀ᶠ u in 𝓝 (BV.chart j x), ((BV.chart j).symm u).1 ∈ R.U x.1 := by
  obtain ⟨k, hk⟩ : ∃ k, x.1 ∈ (R.A.chart k).source := R.A.cover x.1
  have hxt : BV.chart j x ∈ (BV.chart j).target := (BV.chart j).map_source hx
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  have hcont : ContinuousAt (fun u => ((BV.chart j).symm u).1) (BV.chart j x) :=
    continuous_subtype_val.continuousAt.comp ((BV.chart j).continuousAt_symm hxt)
  have hev : ∀ s : Set R.X, IsOpen s → x.1 ∈ s →
      ∀ᶠ u in 𝓝 (BV.chart j x), ((BV.chart j).symm u).1 ∈ s := fun s hs hxs =>
    hcont.preimage_mem_nhds (by
      show s ∈ 𝓝 ((BV.chart j).symm (BV.chart j x)).1
      rw [hsx]; exact hs.mem_nhds hxs)
  refine ⟨?_, hev _ (R.isOpen_U x.1) (R.mem_U x.1)⟩
  rw [analyticAt_pi_iff]
  intro p
  have h1 : AnalyticAt ℂ ((fun y => R.lift x.1 y p) ∘ (R.A.chart k).symm) (R.A.chart k x.1) :=
    R.holo x.1 p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k x.1) ∈ R.U x.1
      rw [(R.A.chart k).left_inv hk]; exact R.mem_U x.1⟩
  have h2 : AnalyticAt ℂ (R.A.chart k ∘ Subtype.val ∘ (BV.chart j).symm) (BV.chart j x) :=
    hB.2 j k _ ⟨hxt, by
      show ((BV.chart j).symm (BV.chart j x)).1 ∈ (R.A.chart k).source
      rw [hsx]; exact hk⟩
  refine (h1.comp_of_eq h2 (by simp [hsx])).congr ?_
  filter_upwards [hev _ (R.A.chart k).open_source hk] with u hu
  simp [(R.A.chart k).left_inv hu]

theorem proj_analyticAt {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) {j : Fin BV.n} (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ (fun u => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1))) (BV.chart j x) := by
  classical
  have hF := (lift_analyticAt hB x hx).1
  have hs : AnalyticAt ℂ (fun u => segre (R.lift x.1 ((BV.chart j).symm u).1))
      (BV.chart j x) := by
    rw [analyticAt_pi_iff]
    intro i
    exact Finset.univ.analyticAt_fun_prod (fun k _ => analyticAt_pi_iff.1 hF ⟨k, i k⟩)
  exact ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp hs

theorem analyticAt_chart {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) (h0 : Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0) (j : Fin BV.n)
    (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm) (BV.chart j x) := by
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  have hc : ∀ i : Fin (n + 1), AnalyticAt ℂ
      (fun u => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) i) (BV.chart j x) :=
    fun i => analyticAt_pi_iff.1 (proj_analyticAt Ψ hB x hx) i
  have hG : AnalyticAt ℂ (fun u (i : Fin n) => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) i.succ /
      Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) 0) (BV.chart j x) := by
    rw [analyticAt_pi_iff]
    intro i
    exact (hc i.succ).div (hc 0) (by simpa [hsx] using h0)
  refine hG.congr ?_
  filter_upwards [(lift_analyticAt hB x hx).2] with u hu
  exact (projCoord_eq Ψ hu).symm

theorem det_ne_zero_of_chart {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (y : V) (h0 : Ψ (segre (R.lift y.1 y.1)) 0 ≠ 0)
    {j k : Fin BV.n} (hj : y ∈ (BV.chart j).source) (hk : y ∈ (BV.chart k).source)
    (hd : LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm)
      (BV.chart k y) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) :
    LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm)
      (BV.chart j y) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
  have hu0 : BV.chart j y ∈ (BV.chart j).target := (BV.chart j).map_source hj
  have hv0 : BV.chart k y ∈ (BV.chart k).target := (BV.chart k).map_source hk
  have hsj : (BV.chart j).symm (BV.chart j y) = y := (BV.chart j).left_inv hj
  have hsk : (BV.chart k).symm (BV.chart k y) = y := (BV.chart k).left_inv hk
  have hτu : (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y) = BV.chart k y := by simp [hsj]
  have hτ : AnalyticAt ℂ (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y) :=
    BV.holo j k _ ⟨hu0, by
      show (BV.chart j).symm (BV.chart j y) ∈ (BV.chart k).source; rw [hsj]; exact hk⟩
  have hσ : AnalyticAt ℂ (BV.chart j ∘ (BV.chart k).symm)
      ((BV.chart k ∘ (BV.chart j).symm) (BV.chart j y)) := by
    rw [hτu]
    exact BV.holo k j _ ⟨hv0, by
      show (BV.chart k).symm (BV.chart k y) ∈ (BV.chart j).source; rw [hsk]; exact hj⟩
  have hev : ∀ᶠ u in 𝓝 (BV.chart j y), (BV.chart j).symm u ∈ (BV.chart k).source :=
    ((BV.chart j).continuousAt_symm hu0).preimage_mem_nhds (by
      show (BV.chart k).source ∈ 𝓝 ((BV.chart j).symm (BV.chart j y))
      rw [hsj]; exact (BV.chart k).open_source.mem_nhds hk)
  have hid : (BV.chart j ∘ (BV.chart k).symm) ∘ (BV.chart k ∘ (BV.chart j).symm)
      =ᶠ[𝓝 (BV.chart j y)] id := by
    filter_upwards [hev, (BV.chart j).open_target.mem_nhds hu0] with u hu hut
    simp [(BV.chart k).left_inv hu, (BV.chart j).right_inv hut]
  have hq : (projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm =ᶠ[𝓝 (BV.chart j y)]
      ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm) ∘ (BV.chart k ∘ (BV.chart j).symm) := by
    filter_upwards [hev] with u hu
    simp [(BV.chart k).left_inv hu]
  have hqk : DifferentiableAt ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm)
      ((BV.chart k ∘ (BV.chart j).symm) (BV.chart j y)) := by
    rw [hτu]; exact (analyticAt_chart Ψ hB y h0 k hk).differentiableAt
  have hinv : (fderiv ℂ (BV.chart j ∘ (BV.chart k).symm)
      ((BV.chart k ∘ (BV.chart j).symm) (BV.chart j y))).comp
      (fderiv ℂ (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y)) =
      ContinuousLinearMap.id ℂ (Fin n → ℂ) := by
    rw [← fderiv_comp _ hσ.differentiableAt hτ.differentiableAt, hid.fderiv_eq, fderiv_id]
  have hdetτ : LinearMap.det (fderiv ℂ (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
    intro h
    have := congrArg (fun f : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) =>
      LinearMap.det (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) hinv
    simp [LinearMap.det_comp, h] at this
  rw [hq.fderiv_eq, fderiv_comp _ hqk hτ.differentiableAt, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, hτu]
  exact mul_ne_zero hd hdetτ

theorem proof : ProjRegular.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB
  refine ⟨?_, fun x h0 j hx => analyticAt_chart Ψ hB x h0 j hx, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro x ⟨h0, hdet⟩
    have hj : x ∈ (BV.chart (chartIdx BV x)).source := Classical.choose_spec (BV.cover x)
    have hsx : (BV.chart (chartIdx BV x)).symm (BV.chart (chartIdx BV x) x) = x :=
      (BV.chart _).left_inv hj
    have hg : BV.chart (chartIdx BV x) x ∈ goodT BV (projCoord R Ψ ∘ Subtype.val) (chartIdx BV x) :=
      ⟨(BV.chart _).map_source hj, analyticAt_chart Ψ hB x h0 _ hj, hdet _ hj⟩
    have hD : ∀ᶠ u in 𝓝 (BV.chart (chartIdx BV x) x),
        Ψ (segre (R.lift x.1 ((BV.chart (chartIdx BV x)).symm u).1)) 0 ≠ 0 :=
      (analyticAt_pi_iff.1 (proj_analyticAt Ψ hB x hj) 0).continuousAt.eventually_ne
        (by simpa [hsx] using h0)
    refine ((BV.chart _).eventually_nhds' (· ∈ projRegular R Ψ BV) hj).1 ?_
    filter_upwards [(isOpen_goodT BV _ _).mem_nhds hg, hD, (lift_analyticAt hB x hj).2]
      with u hu hDu hUu
    have h0u := (proj_ne_zero_iff Ψ hUu).2 hDu
    refine ⟨h0u, fun k hk => det_ne_zero_of_chart Ψ hB _ h0u hk ((BV.chart _).map_target hu.1) ?_⟩
    rw [(BV.chart _).right_inv hu.1]
    exact hu.2.2
  · intro x h0 hd
    exact ⟨h0, fun k hk => det_ne_zero_of_chart Ψ hB x h0 hk
      (Classical.choose_spec (BV.cover x)) hd⟩

end ProjRegular

end GroundTheory.Heights₂.Heights.Targets
