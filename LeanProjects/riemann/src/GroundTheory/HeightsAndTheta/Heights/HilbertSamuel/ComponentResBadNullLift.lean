import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResBadNull
import GroundTheory.HeightsAndTheta.Heights.Intersections.UnitChartOperator
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

omit [Fintype K] in

theorem homogD : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal R.D :=
  (GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff R.D).mp R.homog

theorem mem_D_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : ReciprocityTheory.AnForm.R.SameOrbit z z')
    (hz' : z' ∈ ReciprocityTheory.AnForm.R.conePts R.D) : z ∈ ReciprocityTheory.AnForm.R.conePts R.D := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul (homogD R) c z' hz'.2⟩
  obtain ⟨i, hi⟩ := hz'.1 k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : ReciprocityTheory.AnForm.R.SameOrbit z z') :
    ReciprocityTheory.AnForm.R.SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  rw [← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

theorem pt_mem_D_iff {x y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) :
    R.pt y ∈ ReciprocityTheory.AnForm.R.conePts R.D ↔ R.liftAt x y ∈ ReciprocityTheory.AnForm.R.conePts R.D := by
  have h := GroundTheory.Heights₂.Heights.Inter.res_compat R x y hy (R.mem_src_idx y)
  exact ⟨fun hp => mem_D_of_sameOrbit R h hp, fun hl => mem_D_of_sameOrbit R (sameOrbit_symm h) hl⟩

theorem psi_pt_eq {x y : R.R.M} (hy : y ∈ R.R.src (R.idx x))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (R.pt y)) = μ • Ψ (segre (R.liftAt x y)) := by
  obtain ⟨c, hc, hyc⟩ := GroundTheory.Heights₂.Heights.Inter.res_compat R y x (R.mem_src_idx y) hy
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, ?_⟩
  rw [show R.pt y = R.liftAt y y from rfl, hyc, segre_smul, map_smul]

theorem resProj_eq_local (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x y : R.R.M}
    (hy : y ∈ R.R.src (R.idx x)) :
    resProj R Ψ y = fun i => Ψ (segre (R.liftAt x y)) i.succ / Ψ (segre (R.liftAt x y)) 0 := by
  obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R hy Ψ
  funext i
  simp only [resProj, hμeq, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hμ

theorem analyticAt_segre_liftAt (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M)
    (j : Fin R.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v)))) u := by
  have hl := R.analyticAt_liftAt_pi x j hu
  have hs : AnalyticAt ℂ (fun v => segre (R.liftAt x ((R.atlas.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

theorem analyticAt_resProj (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M)
    (j : Fin R.atlas.n) (hj : x ∈ (R.atlas.chart j).source) (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) :
    AnalyticAt ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) := by
  set u := R.atlas.chart j x
  have hsu : (R.atlas.chart j).symm u = x := (R.atlas.chart j).left_inv hj
  have hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x) :=
    ⟨(R.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_src_idx x⟩
  have hH := analyticAt_segre_liftAt R Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (R.liftAt x ((R.atlas.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) i.succ /
        Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis (R.idx x))).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (resProj_eq_local R Ψ hv.2).symm

theorem det_resProj_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.R.M}
    {j k : Fin R.atlas.n} (hj : x ∈ (R.atlas.chart j).source) (hk : x ∈ (R.atlas.chart k).source)
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart k).symm) (R.atlas.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (R.atlas.chart k ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  set u := R.atlas.chart j x
  have hsu : (R.atlas.chart j).symm u = x := (R.atlas.chart j).left_inv hj
  set T := R.atlas.chart k ∘ (R.atlas.chart j).symm with hTdef
  have huk : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' (R.atlas.chart k).source :=
    ⟨(R.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := R.atlas.holo j k u huk
  have hTu : T u = R.atlas.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_resProj R Ψ x k hk h0
  have heq : resProj R Ψ ∘ (R.atlas.chart j).symm =ᶠ[𝓝 u] (resProj R Ψ ∘ (R.atlas.chart k).symm) ∘ T := by
    filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.atlas.chart k).open_source).mem_nhds
      huk] with v hv
    simp only [hTdef, Function.comp_apply, (R.atlas.chart k).left_inv hv.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt, hTu]
  exact LinearMap.det_comp _ _

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem mcPts_of_conePts {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ ReciprocityTheory.AnForm.R.conePts W) : z ∈ mcPts P :=
  ⟨hz.1, fun _ hf => hz.2 _ (hW.1.2 (Ideal.mem_map_of_mem _ hf))⟩

theorem pt_mem_mcPts {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) (x : R.R.M) :
    R.pt x ∈ mcPts P :=
  mcPts_of_conePts hW (GroundTheory.Heights₂.Heights.Inter.res_mem R x (R.mem_src_idx x))

def resW (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.pt x)) 0)⁻¹ • segre (R.pt x)

theorem resW_mem_fibre {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) (hK : Nonempty K)
    (hPh : IsMultiHomogIdeal P) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.R.M}
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) : resW R Ψ x ∈ fibre P Ψ (resProj R Ψ x) := by
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.pt x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (R.pt x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * R.pt x p, mcPts_smul hPh c hc (pt_mem_mcPts R hW x), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [resW, h0]
    · simp only [resW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, resProj]
      rw [div_eq_inv_mul]

theorem resW_injOn (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set.InjOn (resW R Ψ) {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.R.inj (R.idx x) (R.idx x') x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ?_
  have hseg : segre (R.pt x) = (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) • segre (R.pt x') := by
    have := congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw
    simp only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
    exact this
  obtain ⟨c, hc, h⟩ := sameOrbit_of_segre
    (GroundTheory.Heights₂.Heights.Inter.res_mem R x' (R.mem_src_idx x')).1
    (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) (by simp [hx.2, hx'.2]) hseg
  exact ⟨c, hc, h⟩

theorem resFib_finite {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (resProj R Ψ ⁻¹' {y} ∩
      {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0}).Finite := by
  refine Set.Finite.of_finite_image (f := resW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((resW_injOn R Ψ).mono fun x hx => hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := resW_mem_fibre R hW hP.1 hP.2.1.2.1 Ψ hx.2.2
  rwa [show resProj R Ψ x = y from hx.1] at this

end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
