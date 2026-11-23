import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPerPoint
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPolyDelta
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.per_int

theorem c2on {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (th : LocPot X)
    (ph : X → ℝ) (hth : IsPotential A th) (hph : A.SmoothOn U ph) (x : X) (k : Fin A.n) :
    ContDiffOn ℝ 2 ((th + LocPot.ofFun ph).φ x ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (th.U x ∩ U)) :=
  ((potSmoothOn A th hth x k).mono fun _ hy => ⟨hy.1, hy.2.1⟩).add
    (((hph k).of_le (WithTop.coe_le_coe.2 le_top)).mono fun _ hy => ⟨hy.1, hy.2.2⟩)

theorem c2at {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (hU : IsOpen U)
    (th : LocPot X) (ph : X → ℝ) (hth : IsPotential A th) (hph : A.SmoothOn U ph) (x : X) (k : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (th.U x ∩ U)) :
    ContDiffAt ℝ 2 ((th + LocPot.ofFun ph).φ x ∘ (A.chart k).symm) y :=
  (c2on A U th ph hth hph x k).contDiffAt
    (((A.chart k).isOpen_inter_preimage_symm ((th.isOpen_U x).inter hU)).mem_nhds hy)

theorem dens_cont {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (hU : IsOpen U)
    (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (hth : ∀ i, IsPotential A (th i))
    (hph : ∀ i, A.SmoothOn U (ph i)) (j : Fin A.n) (y₀ : Fin e → ℂ) (hy₀ : y₀ ∈ (A.chart j).target)
    (hyU : (A.chart j).symm y₀ ∈ U) :
    ContinuousAt (locDens A (fun i => th i + LocPot.ofFun (ph i)) j) y₀ := by
  set x₀ := (A.chart j).symm y₀ with hx₀
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((⋂ i, (th i).U x₀) ∩ U)) :=
    (A.chart j).isOpen_inter_preimage_symm ((isOpen_iInter_of_finite fun i => (th i).isOpen_U _).inter hU)
  have hyV : y₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ((⋂ i, (th i).U x₀) ∩ U) :=
    ⟨hy₀, Set.mem_iInter.2 fun i => (th i).mem_U _, hyU⟩
  have heq : maDens (fun i => (th i + LocPot.ofFun (ph i)).φ x₀ ∘ (A.chart j).symm) =ᶠ[𝓝 y₀]
      locDens A (fun i => th i + LocPot.ofFun (ph i)) j := by
    filter_upwards [hVo.mem_nhds hyV] with y hy
    symm
    unfold locDens
    apply maDens_congr_hessC
    intro i
    have hx := Set.mem_iInter.1 hy.2.1 i
    obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ := (hth i).2 ((A.chart j).symm y) x₀ _ ⟨(th i).mem_U _, hx⟩
    have hn : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U x₀) ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm
        ((hWo.inter ((th i).isOpen_U _)).inter ((th i).isOpen_U _))).mem_nhds ⟨hy.1, ⟨hyW, (th i).mem_U _⟩, hx⟩
    have h1 : (fun y' => (th i + LocPot.ofFun (ph i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
        fun w => ((th i + LocPot.ofFun (ph i)).φ x₀ ∘ (A.chart j).symm) w + ((G ∘ (A.chart j).symm) w).re := by
      filter_upwards [hn] with w hw
      have := hGeq _ hw.2
      show (th i).φ ((A.chart j).symm y) ((A.chart j).symm w) + ph i ((A.chart j).symm w) =
        (th i).φ x₀ ((A.chart j).symm w) + ph i ((A.chart j).symm w) + (G ((A.chart j).symm w)).re
      linarith
    rw [hessCGerm _ _ _ h1]
    exact ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _
      (c2at A U hU _ _ (hth i) (hph i) x₀ j ⟨hy.1, hx, hy.2.2⟩) (hG j y ⟨hy.1, hyW⟩)
  refine ContinuousAt.congr ?_ heq
  refine (maDens_continuousOn _ _ hVo fun i => ?_).continuousAt (hVo.mem_nhds hyV)
  exact (c2on A U _ _ (hth i) (hph i) x₀ j).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.1 i, hy.2.2⟩

theorem cont_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (f : X → ℝ) (hf : A.Smooth f)
    (j : Fin A.n) (y : Fin e → ℂ) (hy : y ∈ (A.chart j).target) : ContinuousAt (f ∘ (A.chart j).symm) y :=
  (hf j).continuousOn.continuousAt (by simpa using (A.chart j).open_target.mem_nhds hy)

end PositivityTheory.Xgp.per_int

open PositivityTheory.Xgp.per_int in

theorem PositivityTheory.Xgp.t_per_int : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (U : Set X) (th : Ψ × Fin N → LocPot X) (ph : Ψ × Fin N → X → ℝ), j ≤ N → e = antisymDegree Ψ N → IsOpen U → IsNull A Uᶜ → (∀ p, IsPotential A (th p)) → (∀ p, A.SmoothOn U (ph p)) → IsUniformised A U j (fun p => th p + LocPot.ofFun (ph p)) → (∀ w : Fin e → Ψ × Fin N, MIntegrable A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) → ∃ v : ℝ, 0 < v ∧ toWt (formPoly e fun w => mInt A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) = C v * antisymDelta Ψ N := by
  intro e X _ _ _ A Ψ _ _ N j U th ph hj he hU hN hth hph hun hI
  let pot : Ψ × Fin N → LocPot X := fun p => th p + LocPot.ofFun (ph p)
  let Pc : (Ψ × Fin N → ℝ) → ℝ := fun c => ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)
  have hP1 : 0 < Pc fun _ => 1 :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l hl =>
      Finset.sum_pos (fun _ _ => one_pos) ⟨i, Finset.mem_Ico.2 ⟨le_rfl, Finset.mem_Ioi.1 hl⟩⟩
  have hC : ∀ a, ∀ x ∈ U, IsTwiceDifferentiableAt A (pot a) x := fun a x hx k hk =>
    c2at A U hU _ _ (hth a) (hph a) x k
      ⟨(A.chart k).map_source hk, by simpa [(A.chart k).left_inv hk] using ⟨(th a).mem_U x, hx⟩⟩
  have hexp := fun c : Ψ × Fin N → ℝ => mInt_sumPot_expand e X A _ U pot (fun _ => c) (fun _ => 1) hN hC hI
  have hpt : ∀ k, ∀ᵐ y, y ∈ (A.chart k).target → ∃ ν : ℝ, 0 ≤ ν ∧
      ∀ c, locDens A (fun _ => sumPot c pot) k y = ν * Pc c := fun k => by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN k)] with y hy hyt
    have hyU : (A.chart k).symm y ∈ U := by
      by_contra h
      exact hy ⟨hyt, h⟩
    obtain ⟨V, g, hg⟩ := hun.1 _ hyU
    obtain ⟨ν, h0, -, h⟩ := PositivityTheory.Xgp.t_per_point e X A Ψ N j hj pot _ V g hg he k ((A.chart k).map_target hyt)
    rw [(A.chart k).right_inv hyt] at h
    exact ⟨ν, h0, h⟩
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hprop : ∀ c, mInt A (fun _ => sumPot c pot) (fun _ => 1) =
      mInt A (fun _ => sumPot (fun _ => 1) pot) (fun _ => 1) / (Pc fun _ => 1) * Pc c := fun c => by
    simp only [mInt, dif_pos hne, integralWith]
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_div, ← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hpt k), ae_restrict_mem (A.chart k).open_target.measurableSet] with y hy hyt
    obtain ⟨ν, -, h⟩ := hy hyt
    rw [h, h]
    field_simp
  have hpos : 0 < mInt A (fun _ => sumPot (fun _ => 1) pot) (fun _ => 1) := by
    simp only [mInt, dif_pos hne, integralWith]
    have hnn : ∀ k, 0 ≤ᵐ[volume.restrict (A.chart k).target] fun y => hne.some.χ k ((A.chart k).symm y) * 1 *
        locDens A (fun _ => sumPot (fun _ => 1) pot) k y := fun k => by
      filter_upwards [ae_restrict_of_ae (hpt k), ae_restrict_mem (A.chart k).open_target.measurableSet] with y hy hyt
      obtain ⟨ν, h0, h⟩ := hy hyt
      have := hne.some.nonneg k ((A.chart k).symm y)
      rw [h]
      positivity
    obtain ⟨x, hx, V, g, hg, him⟩ := hun.2
    obtain ⟨k, hk⟩ : ∃ k, hne.some.χ k x ≠ 0 := by
      by_contra h
      push Not at h
      have := hne.some.sum_eq_one x
      simp [h] at this
    have hxk : x ∈ (A.chart k).source := hne.some.tsupport_subset k (subset_tsupport _ hk)
    have hyt := (A.chart k).map_source hxk
    have hsx := (A.chart k).left_inv hxk
    refine Finset.sum_pos' (fun k _ => integral_nonneg_of_ae (hnn k)) ⟨k, Finset.mem_univ _, ?_⟩
    refine (setIntegral_pos_iff_support_of_nonneg_ae (hnn k)
      (integrableOn_weight A hne.some _ (fun _ => 1) (hexp fun _ => 1).1 k)).2 ?_
    have hcd : ContinuousAt (locDens A (fun _ => sumPot (fun _ => 1) pot) k) (A.chart k x) := by
      have h1 : ContinuousAt (fun y => ∑ w : Fin e → Ψ × Fin N, (∏ _i : Fin e, (1 : ℝ)) *
          locDens A (fun i => pot (w i)) k y) (A.chart k x) :=
        tendsto_finset_sum _ fun w _ => continuousAt_const.mul
          (dens_cont A U hU _ _ (fun i => hth (w i)) (fun i => hph (w i)) k _ hyt (by rwa [hsx]))
      refine h1.congr ?_
      filter_upwards [((A.chart k).isOpen_inter_preimage_symm hU).mem_nhds ⟨hyt, show _ ∈ U by rwa [hsx]⟩] with y hy
      exact (locDens_sumPot_expand A pot (fun _ _ => 1) k hy.1 fun a => hC a _ hy.2).symm
    have hcf : ContinuousAt (fun y => hne.some.χ k ((A.chart k).symm y) * 1 *
        locDens A (fun _ => sumPot (fun _ => 1) pot) k y) (A.chart k x) :=
      ((cont_chart A _ (hne.some.smooth k) k _ hyt).mul continuousAt_const).mul hcd
    obtain ⟨ν, -, hν, h⟩ := PositivityTheory.Xgp.t_per_point e X A Ψ N j hj pot x V g hg he k hxk
    have hv : hne.some.χ k ((A.chart k).symm (A.chart k x)) * 1 *
        locDens A (fun _ => sumPot (fun _ => 1) pot) k (A.chart k x) ≠ 0 := by
      rw [h, hsx]
      exact mul_ne_zero (mul_ne_zero hk one_ne_zero) (mul_pos (hν him) hP1).ne'
    exact Measure.measure_pos_of_mem_nhds _ (inter_mem (hcf.eventually_ne hv) ((A.chart k).open_target.mem_nhds hyt))
  refine ⟨_, div_pos hpos hP1, (PositivityTheory.Xgp.t_poly_delta Ψ N _ _ fun c => ?_).1⟩
  rw [← hprop c, (hexp c).2]
  simp only [formPoly, map_sum, map_mul, eval_C, map_prod, eval_X]
  exact Finset.sum_congr rfl fun w _ => mul_comm _ _
