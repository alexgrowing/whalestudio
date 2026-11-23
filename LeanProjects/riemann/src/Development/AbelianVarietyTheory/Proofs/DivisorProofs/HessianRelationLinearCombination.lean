import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentMapContinuousSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianOfCombinationMetricLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownwardChartLocalHolomorphicSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianZeroOfLeviZeroStatement
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

open scoped ContDiff
open ReciprocityTheory.L2DbarEstimates (cHess)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.HessComb

theorem cHess_sum {n : ℕ} {ι : Type} (s : Finset ι) {Ω : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hΩ : IsOpen Ω) (q : ι → ReciprocityTheory.L2DbarEstimates.V n → ℝ)
    (hq : ∀ l, ContDiffOn ℝ ∞ (q l) Ω) (t : ι → ℝ) (g : ReciprocityTheory.L2DbarEstimates.V n → ℝ) (hg : ContDiffOn ℝ ∞ g Ω) {y : ReciprocityTheory.L2DbarEstimates.V n} (hy : y ∈ Ω) :
    cHess n (fun w => ((g w + ∑ l ∈ s, t l * q l w : ℝ) : ℂ)) y =
      cHess n (fun w => (g w : ℂ)) y + ∑ l ∈ s, (t l : ℂ) • cHess n (fun w => (q l w : ℂ)) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    have he : (fun w => ((g w + ∑ l ∈ insert b s, t l * q l w : ℝ) : ℂ)) =
        fun w => (((g w + ∑ l ∈ s, t l * q l w) + t b * q b w : ℝ) : ℂ) := by
      funext w
      rw [Finset.sum_insert hb]
      push_cast
      ring
    have hs : ContDiffOn ℝ ∞ (fun w => g w + ∑ l ∈ s, t l * q l w) Ω :=
      hg.add (ContDiffOn.sum fun l _ => contDiffOn_const.mul (hq l))
    rw [he, ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hΩ hs (hq b) (t b) hy, ih, Finset.sum_insert hb]
    abel

theorem hessRel_comb : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB V.p) (P : ι → M.Pot) (n : ι → ℤ) (R : M.Pot), (∀ i a, ReciprocityTheory.AnForm.M.IsPotential (M.A a) (P i a)) → (∀ a, ReciprocityTheory.AnForm.M.IsPotential (M.A a) (R a)) → (∀ i, HessRel ε π (L i) (P i)) → (∀ a j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, leviAt (M.A a) (R a) j y w = ∑ i, (n i : ℝ) * leviAt (M.A a) (P i a) j y w) → HessRel ε π (ArInt.comb L n) R := by
  intro F _ _ Y V e M I ε π hd ι _ L P n R hP hR hL hlevi σ c y hy i hi
  obtain ⟨j, hj⟩ := (M.A (ε σ)).cover (π σ y)
  obtain ⟨U, hU, hyU, -, hUs, hτ⟩ := GlobalTheory.T.downward_chart_local_holomorphic_section F Y V e M I ε π hd σ c y hy j hj
  set ch := (M.A (ε σ)).chart j with hch
  set x₀ := π σ y with hx₀
  set τ : ReciprocityTheory.L2DbarEstimates.V e → ReciprocityTheory.L2DbarEstimates.V e := fun v => FinChart.toV e (ch (π σ (c.e.symm v))) with hτdef
  set T := (FinChart.toV e).symm with hT

  set gR : (Fin e → ℂ) → ℝ := (R (ε σ)).φ x₀ ∘ ch.symm with hgR
  set gP : ι → (Fin e → ℂ) → ℝ := fun l => (P l (ε σ)).φ x₀ ∘ ch.symm with hgP
  set S : Set (Fin e → ℂ) := ch.target ∩ ch.symm ⁻¹' ((R (ε σ)).U x₀ ∩ ⋂ l, (P l (ε σ)).U x₀) with hS
  have hSo : IsOpen S := ch.isOpen_inter_preimage_symm
    (((R (ε σ)).isOpen_U x₀).inter (isOpen_iInter_of_finite fun l => (P l (ε σ)).isOpen_U x₀))
  have hsR : ContDiffOn ℝ ∞ gR S := ((hR (ε σ)).1 x₀ j).mono fun z hz => ⟨hz.1, hz.2.1⟩
  have hsP (l : ι) : ContDiffOn ℝ ∞ (gP l) S :=
    ((hP l (ε σ)).1 x₀ j).mono fun z hz => ⟨hz.1, Set.mem_iInter.1 hz.2.2 l⟩
  have hτc : ContDiffOn ℝ ∞ (fun v => T (τ v)) U :=
    T.contDiff.comp_contDiffOn ((show ContDiffOn ℂ ∞ τ U from ((SCV.analyticOnNhd_iff_differentiableOn hU).2 hτ).contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ)
  set Ω := U ∩ (fun v => T (τ v)) ⁻¹' S with hΩ
  have hΩo : IsOpen Ω := hτc.continuousOn.isOpen_inter_preimage hU hSo
  have hz₀ : T (τ (c.e y)) = ch x₀ := by
    show T (FinChart.toV e (ch (π σ (c.e.symm (c.e y))))) = ch x₀
    rw [hT, ContinuousLinearEquiv.symm_apply_apply, c.e.left_inv hy]
  have hyΩ : c.e y ∈ Ω := by
    refine ⟨hyU, ?_⟩
    show T (τ (c.e y)) ∈ S
    rw [hz₀]
    refine ⟨ch.map_source hj, ?_⟩
    rw [Set.mem_preimage, ch.left_inv hj]
    exact ⟨(R (ε σ)).mem_U x₀, Set.mem_iInter.2 fun l => (P l (ε σ)).mem_U x₀⟩
  have hback (v : ReciprocityTheory.L2DbarEstimates.V e) (hv : v ∈ Ω) : ch.symm (T (τ v)) = π σ (c.e.symm v) := by
    simp only [hτdef, hT, ContinuousLinearEquiv.symm_apply_apply]
    exact ch.left_inv (hUs v hv.1)
  have hmaps : Set.MapsTo (fun v => T (τ v)) Ω S := fun v hv => hv.2
  have hcR : ContDiffOn ℝ ∞ (fun v => gR (T (τ v))) Ω := hsR.comp (hτc.mono Set.inter_subset_left) hmaps
  have hcP (l : ι) : ContDiffOn ℝ ∞ (fun v => gP l (T (τ v))) Ω := (hsP l).comp (hτc.mono Set.inter_subset_left) hmaps

  rw [GlobalTheory.T.hessian_of_combination_metric_linear L n σ c hy i hi (fun l => pick (L l).isLB y) (fun l => mem_pick _ y)]
  simp_rw [fun l => hL l σ c y hy (pick (L l).isLB y) (mem_pick _ y)]

  set G : (Fin e → ℂ) → ℝ := fun z => ∑ l ∈ Finset.univ, (-(2 * (n l : ℝ))) * gP l z + 2 * gR z with hG
  have hz₀t : ch x₀ ∈ ch.target := ch.map_source hj
  have hsym : ch.symm (ch x₀) = x₀ := ch.left_inv hj
  have hc2P (l : ι) : ContDiffAt ℝ 2 (gP l) (ch x₀) := by
    have := Deg.potential_chart_contDiffAt_two (M.A (ε σ)) (hP l (ε σ)) j hz₀t
    rwa [hsym] at this
  have hc2R : ContDiffAt ℝ 2 gR (ch x₀) := by
    have := Deg.potential_chart_contDiffAt_two (M.A (ε σ)) (hR (ε σ)) j hz₀t
    rwa [hsym] at this
  have hGl (w : Fin e → ℂ) : levi G (ch x₀) w = 0 := by
    have h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) (ch x₀) w = 0 := by simp [levi]
    have h2 := levi_add_smul (f := fun _ : Fin e → ℂ => (0 : ℝ)) 2 contDiffAt_const hc2R w
    simp only [zero_add, h0] at h2
    have := (LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.levi_sum_add Finset.univ (fun l => -(2 * (n l : ℝ))) gP
      (fun z => 2 * gR z) hc2P (contDiffAt_const.mul hc2R) w).2
    have hl' : levi gR (ch x₀) w = ∑ l, (n l : ℝ) * levi (gP l) (ch x₀) w := by
      have hl := hlevi (ε σ) j (ch x₀) hz₀t w
      simp only [leviAt, ← hch, hsym] at hl
      exact hl
    rw [hG, this, h2, hl', Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun l _ => by ring
  have hGc : ContDiffAt ℝ 2 G (ch x₀) :=
    (LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.levi_sum_add Finset.univ (fun l => -(2 * (n l : ℝ))) gP
      (fun z => 2 * gR z) hc2P (contDiffAt_const.mul hc2R) 0).1
  have hzero := GlobalTheory.T.complex_hessian_zero_of_levi_zero G τ hU hyU hτ (by rwa [hz₀]) (by rwa [hz₀])
  have hGs : ContDiffOn ℝ ∞ (fun v => G (T (τ v))) Ω := by
    simp only [hG]
    exact (ContDiffOn.sum fun l _ => contDiffOn_const.mul (hcP l)).add (contDiffOn_const.mul hcR)
  have key := cHess_sum Finset.univ hΩo (fun l v => 2 * gP l (T (τ v))) (fun l => contDiffOn_const.mul (hcP l))
    (fun l => (n l : ℝ)) (fun v => G (T (τ v))) hGs hyΩ
  rw [hzero, zero_add] at key
  calc _ = ∑ l, ((n l : ℝ) : ℂ) • cHess e (fun w => ((2 * gP l (T (τ w)) : ℝ) : ℂ)) (c.e y) := by
          refine Finset.sum_congr rfl fun l _ => congrArg _ (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_)
          filter_upwards [hΩo.mem_nhds hyΩ] with v hv
          simp only [hgP, Function.comp_apply, hback v hv, hx₀]
    _ = _ := key.symm
    _ = _ := by
          refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
          filter_upwards [hΩo.mem_nhds hyΩ] with v hv
          have e₁ : gR (T (τ v)) = (R (ε σ)).φ x₀ (π σ (c.e.symm v)) := by
            simp only [hgR, Function.comp_apply, hback v hv]
          rw [← e₁, hG]
          push_cast
          rw [add_right_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero (fun l _ => by ring), zero_add]

end GlobalTheory.Mean4O.HessComb
