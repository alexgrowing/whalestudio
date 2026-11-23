import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
open GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernTop GlobalTheory.Points
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FubiniStudyChart

open ReciprocityTheory.L2DbarEstimates (V cHess leviV wd wdb sqNorm projPerp wJac)

theorem posDef_cHess_log_sqNorm {n p : ℕ} (g : Fin p → V n → ℂ) (x : V n)
    (hg : ∀ i, ContDiffAt ℂ 2 (g i) x) (b : Fin p) (hb : g b x ≠ 0) (hbd : ∀ j, wd n j (g b) x = 0)
    (hinj : ∀ ξ : Fin n → ℂ, (∀ a, ∑ j, wd n j (g a) x * ξ j = 0) → ξ = 0) :
    (cHess n (fun v => ((Real.log (sqNorm fun i => g i v) : ℝ) : ℂ)) x).PosDef := by
  set f : V n → ℝ := fun v => Real.log (sqNorm fun i => g i v) with hf
  set G : V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hG
  have hne : (fun i => g i x) ≠ 0 := fun h => hb (congrFun h b)
  have hfC : ContDiffAt ℝ 2 f x := by
    have hs : ContDiffAt ℝ 2 (fun v => ∑ i, Complex.normSq (g i v)) x :=
      ContDiffAt.sum fun i _ => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hg i)
    exact hs.log (ReciprocityTheory.L2DbarEstimates.sqNorm_pos hne).ne'
  have hg2 : ContDiffAt ℝ 2 G x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hfC
  have hgc : (fun w => (starRingEnd ℂ) (G w)) = G := funext fun w => by simp [G]
  have hH : (cHess n G x).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show (starRingEnd ℂ) (wd n k (wdb n j G) x) = wd n j (wdb n k G) x
    have h1 : (fun w => (starRingEnd ℂ) (wdb n j G w)) = wd n j G := by
      funext w
      rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' n j G w, hgc]
    rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj' n k (wdb n j G) x, h1,
      ReciprocityTheory.L2DbarEstimates.comm_wd_wdb G x hg2 j k]
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun y hy => ?_⟩
  have hre : star y ⬝ᵥ (cHess n G x *ᵥ y) = leviV n G x (fun k => (starRingEnd ℂ) (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  rw [hre, hG, hf, ReciprocityTheory.L2DbarEstimates.leviLogNormSq n p g x _ hg hne]

  set ξ : Fin n → ℂ := fun k => (starRingEnd ℂ) (y k) with hξ
  set gx : Fin p → ℂ := fun i => g i x
  have hpos : 0 < sqNorm gx := ReciprocityTheory.L2DbarEstimates.sqNorm_pos hne
  refine Complex.zero_lt_real.2 (div_pos (ReciprocityTheory.L2DbarEstimates.sqNorm_pos fun h0 => hy ?_) hpos)
  set w := wJac n p g x *ᵥ ξ with hw
  rw [ReciprocityTheory.L2DbarEstimates.projPerp_mulVec, sub_eq_zero] at h0
  have hwb : w b = 0 := by
    simp only [hw, Matrix.mulVec, dotProduct, wJac, hbd, zero_mul, Finset.sum_const_zero]
  have hc : ((sqNorm gx : ℝ) : ℂ)⁻¹ * (star gx ⬝ᵥ w) = 0 := by
    have := congrFun h0 b
    rw [hwb, Pi.smul_apply, smul_eq_mul, eq_comm, mul_eq_zero] at this
    exact this.resolve_right hb
  rw [hc, zero_smul] at h0
  have hξ0 : ξ = 0 := hinj ξ fun a => by
    have := congrFun h0 a
    simpa [hw, Matrix.mulVec, dotProduct, wJac] using this
  funext k
  have := congrFun hξ0 k
  simpa [hξ] using this

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped GlobalTheory.ProjSpace

theorem etale_ratio (k : Type) [CommRing k] (N : ℕ) (i : Fin (N + 1)) :
    (MvPolynomial.eval₂Hom (algX (PSpace.str k N) (ProjSpace.chart k N i))
      (fun a : Fin N => ProjSpace.ratio k N i (i.succAbove a))).Etale := by
  let e : MvPolynomial (Fin N) k ≃ₐ[k] Γ(PSpace k N, ProjSpace.chart k N i) :=
    (MvPolynomial.renameEquiv k (finSuccAboveEquiv i)).trans (ProjSpace.chartAlgEquiv k N i)
  have he : MvPolynomial.eval₂Hom (algX (PSpace.str k N) (ProjSpace.chart k N i))
      (fun a => ProjSpace.ratio k N i (i.succAbove a)) = (e : MvPolynomial (Fin N) k →+* _) :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans (e.commutes a).symm)
      fun b => (MvPolynomial.eval₂Hom_X' _ _ b).trans
        ((congrArg (ProjSpace.chartAlgEquiv k N i) (MvPolynomial.rename_X _ b)).trans
          (ProjSpace.chartAlgEquiv_X k N i (finSuccAboveEquiv i b))).symm
  rw [he]
  exact RingHom.Etale.of_bijective e.bijective

theorem toLp_eq_sum_bas (N : ℕ) (ξ : Fin N → ℂ) :
    (WithLp.toLp 2 ξ : V N) = ∑ j, ξ j • ReciprocityTheory.L2DbarEstimates.bas N j := by
  ext i
  simp only [ReciprocityTheory.L2DbarEstimates.bas, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  try simp

theorem fubiniStudy_hessian_posDef : ∀ (k : Type) [CommRing k] (N : ℕ) (σ : k →+* ℂ) (c0 : AlgChart (PSpace.str k N) σ N) (z : CxPts (PSpace.str k N) σ), z ∈ c0.e.source → ∀ (b : (ProjSpace.hermitianTwistingSheaf k N).B.ι), z ∈ ptsIn (PSpace.str k N) σ ((ProjSpace.hermitianTwistingSheaf k N).B.U b) → (c0.hess ((ProjSpace.hermitianTwistingSheaf k N).φ σ) b z).PosDef := by
  intro k _ N σ c0 z hz b hb
  change Fin (N + 1) at b
  change z ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N b) at hb
  set g : Fin (N + 1) → V N → ℂ := fun a v =>
    ev (PSpace.str k N) σ (ProjSpace.chart k N b) (ProjSpace.ratio k N b a) (c0.e.symm v) with hg
  have e1 : c0.hess ((ProjSpace.hermitianTwistingSheaf k N).φ σ) b z =
      cHess N (fun v => ((Real.log (sqNorm fun i => g i v) : ℝ) : ℂ)) (c0.e z) := by
    show cHess N _ _ = _
    congr 1
    funext v
    have h := Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N) (ProjSpace.coord k N)
      (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) b (c0.e.symm v)
    refine congrArg (fun r : ℝ => (r : ℂ)) (h.trans ?_)
    simp [sqNorm, Matrix.one_apply, Complex.normSq_eq_norm_sq, g, ev]
  rw [e1]
  set x0 := c0.e z with hx0
  set S := c0.e.target ∩ c0.e.symm ⁻¹' ptsIn (PSpace.str k N) σ (ProjSpace.chart k N b) with hS
  have hSo : IsOpen S := GlobalTheory.ChartGlue.isOpen_over c0.e (isOpen_ptsIn _)
  have hxS : x0 ∈ S := GlobalTheory.ChartGlue.mem_over c0.e hz hb
  have hgd : ∀ a, DifferentiableOn ℂ (g a) S := fun a => c0.holo _ _
  have hgC : ∀ a, ContDiffAt ℂ 2 (g a) x0 := fun a =>
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn N _ S hSo (hgd a)).contDiffAt
      (hSo.mem_nhds hxS)).of_le (by norm_cast)
  have hgD : ∀ a, DifferentiableAt ℂ (g a) x0 := fun a => (hgd a).differentiableAt (hSo.mem_nhds hxS)
  have hb1 : g b =ᶠ[nhds x0] fun _ => 1 := by
    filter_upwards [hSo.mem_nhds hxS] with v hv
    simp only [hg, ProjSpace.ratio, ProjSpace.ratioOn_self]
    rw [ev_eq hv.2, map_one]
  refine posDef_cHess_log_sqNorm g x0 hgC b ?_ ?_ ?_
  · rw [hb1.eq_of_nhds]; exact one_ne_zero
  · intro j
    rw [ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt (hgD b), hb1.fderiv_eq]
    simp
  · intro ξ hξ
    obtain ⟨⟨e, U, hU, x, hx, h₁, h₂, h₃⟩, hzs, hU', hx'⟩ := AlgChart.exists_of_etale (σ := σ)
      (ProjSpace.isAffineOpen_chart k N b) (fun a => ProjSpace.ratio k N b (b.succAbove a))
      (etale_ratio k N b) hb
    dsimp only at hU'
    subst hU'
    dsimp only at hx'
    subst hx'
    set cs : AlgChart (PSpace.str k N) σ N := ⟨e, _, hU, _, hx, h₁, h₂, h₃⟩ with hcs
    set F : V N → V N := cs.e ∘ c0.e.symm with hF
    set F' : V N → V N := c0.e ∘ cs.e.symm with hF'
    set T := c0.e.target ∩ c0.e.symm ⁻¹' cs.e.source with hT
    have hTo : IsOpen T := GlobalTheory.ChartGlue.isOpen_over c0.e cs.e.open_source
    have hxT : x0 ∈ T := GlobalTheory.ChartGlue.mem_over c0.e hz hzs
    have hFd : DifferentiableAt ℂ F x0 := (c0.holo_trans cs).differentiableAt (hTo.mem_nhds hxT)
    have hFx : F x0 = cs.e z := by simp only [hF, Function.comp_apply, hx0, c0.e.left_inv hz]
    have hT' : IsOpen (cs.e.target ∩ cs.e.symm ⁻¹' c0.e.source) :=
      GlobalTheory.ChartGlue.isOpen_over cs.e c0.e.open_source
    have hF'd : DifferentiableAt ℂ F' (F x0) := hFx ▸
      (cs.holo_trans c0).differentiableAt (hT'.mem_nhds (GlobalTheory.ChartGlue.mem_over cs.e hzs hz))
    have hid : F' ∘ F =ᶠ[nhds x0] id := by
      filter_upwards [hTo.mem_nhds hxT] with v hv
      simp only [hF, hF', Function.comp_apply, id, cs.e.left_inv hv.2, c0.e.right_inv hv.1]
    have hcomp : HasFDerivAt id ((fderiv ℂ F' (F x0)).comp (fderiv ℂ F x0)) x0 :=
      (hF'd.hasFDerivAt.comp x0 hFd.hasFDerivAt).congr_of_eventuallyEq hid.symm
    have hone := hcomp.unique (hasFDerivAt_id x0)
    set w : V N := WithLp.toLp 2 ξ with hw
    have hwsum : w = ∑ j, ξ j • ReciprocityTheory.L2DbarEstimates.bas N j := by
      exact toLp_eq_sum_bas N ξ
    have hgw : ∀ a, fderiv ℂ (g a) x0 w = 0 := fun a => by
      have := hξ a
      simp only [ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt (hgD a)] at this
      rw [hwsum, map_sum]
      simpa [mul_comm] using this
    have hdF : fderiv ℂ F x0 w = 0 := by
      ext a
      have hFa : HasFDerivAt (fun v => (F v).ofLp a)
          ((EuclideanSpace.proj (𝕜 := ℂ) a).comp (fderiv ℂ F x0)) x0 :=
        (EuclideanSpace.proj (𝕜 := ℂ) a).hasFDerivAt.comp x0 hFd.hasFDerivAt
      have heq : (fun v => (F v).ofLp a) =ᶠ[nhds x0] g (b.succAbove a) := by
        filter_upwards [hTo.mem_nhds hxT] with v hv
        exact h₂ _ hv.2 a
      have := (hFa.congr_of_eventuallyEq heq.symm).fderiv
      have h2 := hgw (b.succAbove a)
      rw [this] at h2
      simpa using h2
    have hw0 : w = 0 := by
      have := congrArg (fun L : V N →L[ℂ] V N => L w) hone
      simp only [ContinuousLinearMap.comp_apply, hdF, map_zero, ContinuousLinearMap.id_apply] at this
      exact this.symm
    funext j
    have := congrArg (fun u : V N => u.ofLp j) hw0
    simpa [hw] using this

end GlobalTheory.FubiniStudyChart
