import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalConjOfNotGoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalOfGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AutomorphicArithmetic.DivisorFrames.ExistsHolomorphicAdaptedChart
import Development.AutomorphicArithmetic.DivisorFrames.LogRatioMetricsAdapted
import Development.AutomorphicArithmetic.DivisorFrames.LocalMetricLowerBound
import Development.AutomorphicArithmetic.DivisorFrames.ChartMetricLowerBound
import Development.AutomorphicArithmetic.DivisorFrames.CurvatureConnectionBound
import Development.AutomorphicArithmetic.DivisorFrames.HolomorphicBallInnerRegion
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder

section Conn

open GlobalTheory GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal GlobalTheory.CurvInterp ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Filter Topology

private theorem conn_affine {d m : ℕ} (H : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin m) (Fin m) ℂ) (w₀ : ReciprocityTheory.L2DbarEstimates.V d)
    (z ξ : Fin d → ℂ) :
    conn (fun z => (H (w₀ + (EuclideanSpace.equiv (Fin d) ℂ).symm z))ᵀ) z ξ =
      (H (w₀ + (EuclideanSpace.equiv (Fin d) ℂ).symm z))⁻¹ *
        wirt H (w₀ + (EuclideanSpace.equiv (Fin d) ℂ).symm z) ((EuclideanSpace.equiv (Fin d) ℂ).symm ξ) := by
  have key : ∀ (f : ReciprocityTheory.L2DbarEstimates.V d → ℂ) (η : Fin d → ℂ),
      fderiv ℝ (fun z => f (w₀ + (EuclideanSpace.equiv (Fin d) ℂ).symm z)) z η =
        fderiv ℝ f (w₀ + (EuclideanSpace.equiv (Fin d) ℂ).symm z) ((EuclideanSpace.equiv (Fin d) ℂ).symm η) := by
    intro f η
    let L : (Fin d → ℂ) ≃L[ℝ] ReciprocityTheory.L2DbarEstimates.V d :=
      { (EuclideanSpace.equiv (Fin d) ℂ).symm.toLinearEquiv.restrictScalars ℝ with
        continuous_toFun := (EuclideanSpace.equiv (Fin d) ℂ).symm.continuous
        continuous_invFun := (EuclideanSpace.equiv (Fin d) ℂ).continuous }
    have h := L.comp_right_fderiv (f := fun u => f (w₀ + u)) (x := z)
    rw [fderiv_comp_add_left] at h
    exact congrArg (fun T => T η) h
  rw [conn, transpose_transpose]
  congr 1
  ext a b
  simp only [transpose_apply, mdel_apply, del_apply, wirt, dMat, Matrix.smul_apply, Matrix.sub_apply, of_apply]
  rw [key (fun w => H w a b), key (fun w => H w a b), map_smul]

private theorem hodgeLocal' {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    (σ : κ.c.F →+* ℂ) : HodgeLocal x σ := by
  by_cases h : Formalism.L2.PjFree.GoodEmb κ.c σ
  · exact GlobalTheory.T.hodge_local_of_good_embedding D A N j S κ s x σ h
  · refine GlobalTheory.T.hodge_local_conj_of_not_good D A N j S κ s x σ h (GlobalTheory.T.hodge_local_of_good_embedding D A N j S κ s x _ ?_)
    simpa only [Formalism.L2.PjFree.goodOf, if_neg h] using Formalism.L2.PjFree.goodEmb_goodOf κ.c σ

private theorem hodge_conn_le {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    {σ : κ.c.F →+* ℂ} {d : ℕ} {B : Set (ReciprocityTheory.L2DbarEstimates.V d)} {a : ReciprocityTheory.L2DbarEstimates.V d → CxFr s.T.Z σ} (hB : IsOpen B)
    (ha : HolFam B a) (hc : ContinuousOn (fun w => (a w).1) B) {w₀ : ReciprocityTheory.L2DbarEstimates.V d} (hw₀ : w₀ ∈ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ w in 𝓝 w₀, Inner (a w).1 → ∀ (τ : D.host.E →+* ℂ) (ξ : ReciprocityTheory.L2DbarEstimates.V d)
      (v : Fin (S.Dw.mult τ) → ℂ),
      ‖(((x.hodge σ).gram (a w).1 (a w).2 τ)⁻¹ * wirt (fun w => (x.hodge σ).gram (a w).1 (a w).2 τ) w ξ) *ᵥ v‖ ≤
        K * Real.exp (x.r σ (a w).1 / 2) * ‖ξ‖ * ‖v‖ := by
  let L := (EuclideanSpace.equiv (Fin d) ℂ).symm
  let β : (Fin d → ℂ) → ReciprocityTheory.L2DbarEstimates.V d := fun z => w₀ + L z
  have hβ : Differentiable ℂ β := (differentiable_const _).add L.differentiable
  have hB' : IsOpen (β ⁻¹' B) := hB.preimage hβ.continuous
  have h0 : (0 : Fin d → ℂ) ∈ β ⁻¹' B := by simpa [β] using hw₀
  have h1 : IsHolTo (β ⁻¹' B) fun z => (a (β z)).1.1 :=
    LocLift.isHolTo_comp (y := fun w => (a w).1.1) ha.1 hB' hβ.differentiableOn fun _ hz => hz
  have h2 : HolFam (β ⁻¹' B) fun z => a (β z) :=
    ⟨h1, fun ρ i U f => (ha.2 ρ i U f).comp hβ.differentiableOn fun _ hz => hz⟩
  have h3 : ContinuousOn (fun z => (a (β z)).1) (β ⁻¹' B) := hc.comp hβ.continuous.continuousOn fun _ hz => hz
  obtain ⟨ρ, hρ, -, hblk⟩ := hodgeLocal' x σ d _ _ hB' h0 h2 h3
  obtain ⟨c, hc0, hc1, hd⟩ := UpperTheory.holomorphic_ball_inner_region D A N j S κ s x σ d _ (fun z => (a (β z)).1) hB' h0 h1 h3
  obtain ⟨C, hC, hb⟩ := UpperTheory.curvature_connection_bound d _ _ ρ _ _ (fun z => c * Real.exp (-(x.r σ (a (β z)).1) / 2)) hρ hblk
    (hd.mono fun z hz hi => ⟨by positivity, mul_le_one₀ hc1 (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by
      linarith [x.exp_le_r σ (a (β z)).1, Real.exp_pos 1])), hz hi⟩)
  refine ⟨C / c, by positivity, ?_⟩
  have ht : Tendsto (fun w => L.symm (w - w₀)) (𝓝 w₀) (𝓝 0) := by
    have : Continuous fun w => L.symm (w - w₀) := L.symm.continuous.comp (continuous_id.sub continuous_const)
    simpa using this.tendsto w₀
  filter_upwards [ht.eventually hb] with w hw hi τ ξ v
  obtain ⟨z, rfl⟩ : ∃ z, w = β z := ⟨L.symm (w - w₀), by simp [β]⟩
  obtain ⟨η, rfl⟩ := L.surjective ξ
  have e : L.symm (β z - w₀) = z := by simp [β]
  rw [e] at hw
  have h4 := hw hi τ η v
  rw [conn_affine (fun w => (x.hodge σ).gram (a w).1 (a w).2 τ) w₀ z η] at h4
  refine h4.trans ?_
  have h5 : ‖η‖ ≤ ‖L η‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => PiLp.norm_apply_le (L η) i
  have h6 : C / (c * Real.exp (-(x.r σ (a (β z)).1) / 2)) = C / c * Real.exp (x.r σ (a (β z)).1 / 2) := by
    rw [neg_div, Real.exp_neg]; field_simp
  rw [h6]
  gcongr

end Conn

section Flag

open GlobalTheory GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal Filter Topology

private theorem conn_bound : OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (g : ∀ p : GlobalTheory.CxPts (O.var c).str σ, (O.Φ.C c).FrameAt p), GlobalTheory.BdGram.IsHolAdapted O ch U g →
  ∀ y₀ ∈ U, y₀ ∉ offBd O.Φ c σ → ∃ (V : Set (GlobalTheory.CxPts (O.var c).str σ)) (K μ : ℝ), IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ 0 ≤ μ ∧
    ∀ y ∈ V, y ∈ offBd O.Φ c σ → ∀ (τ : D.host.E →+* ℂ) (ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim) (v : Fin (O.S.Dw.mult τ) → ℂ),
      ‖((GlobalTheory.BdGram.gramIn O (x.hodge (embOf O.κ.e σ)) ch g τ (ch.e y))⁻¹ * wirt (GlobalTheory.BdGram.gramIn O (x.hodge (embOf O.κ.e σ)) ch g τ) (ch.e y) ξ - (GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g τ (ch.e y))⁻¹ * wirt (GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g τ) (ch.e y) ξ) *ᵥ v‖ ≤
        K * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) * ‖v‖ := by
  intro D O x P hc hf hr c σ ch U g hA y₀ hy₀U _
  obtain ⟨V3, c₃, C₃, hV3o, hV3, hV3U, hc₃, h3⟩ := UpperTheory.local_metric_lower_bound D O x P hc hf hr c σ ch U g hA y₀ hy₀U
  obtain ⟨V4, c₄, hV4o, hV4, -, hc₄, h4⟩ := UpperTheory.chart_metric_lower_bound D O x P hc hf hr c σ ch y₀ (hA.2.1 hy₀U)
  have hBo : IsOpen (ch.e '' U) := ch.e.isOpen_image_of_subset_source hA.1 hA.2.1
  have hcont : ContinuousOn (fun w => (O.Φ.C c).down (ch.e.symm w)) (ch.e '' U) :=
    (CxPts.continuous_of_comp (m := (O.Φ.C c).down (σ := σ)) (f := (O.Φ.C c).π) (fun _ => rfl)).comp_continuousOn
      (ch.e.continuousOn_symm.mono (by rintro _ ⟨y, hy, rfl⟩; exact ch.e.map_source (hA.2.1 hy)))
  obtain ⟨K, hK, hev⟩ := hodge_conn_le x hBo hA.2.2.2.2.1 hcont (w₀ := ch.e y₀) ⟨y₀, hy₀U, rfl⟩
  obtain ⟨GroupRetwisting, hV5, hV5o, hy5⟩ := mem_nhds_iff.1 ((ch.e.continuousAt (hA.2.1 hy₀U)).eventually hev)
  refine ⟨V3 ∩ V4 ∩ GroupRetwisting, (K + |C₃|) / c₄, 0, (hV3o.inter hV4o).inter hV5o, ⟨⟨hV3, hV4⟩, hy5⟩,
    fun y hy => hV3U hy.1.1, le_rfl, fun y hy hb τ ξ v => ?_⟩
  have hys : y ∈ ch.e.source := hA.2.1 (hV3U hy.1.1)
  have e : ch.e.symm (ch.e y) = y := ch.e.left_inv hys
  have h5 := hV5 hy.2 (by
    show Inner ((O.Φ.C c).down (ch.e.symm (ch.e y)))
    rw [e]; exact hb) τ ξ v
  have er : x.r (embOf O.κ.e σ) ((O.Φ.C c).down (ch.e.symm (ch.e y))) = O.met.r c σ y := by rw [e, hc.r_eq]; rfl
  have h5' : ‖((GlobalTheory.BdGram.gramIn O (x.hodge (embOf O.κ.e σ)) ch g τ (ch.e y))⁻¹ *
      wirt (GlobalTheory.BdGram.gramIn O (x.hodge (embOf O.κ.e σ)) ch g τ) (ch.e y) ξ) *ᵥ v‖ ≤
      K * Real.exp (O.met.r c σ y / 2) * ‖ξ‖ * ‖v‖ := by
    rw [← er]; exact h5
  have h6 := ((h3 y hy.1.1 τ).2 v).2.2 ξ
  have h7 := h4 y hy.1.2 ξ
  have hr0 : 0 ≤ O.met.r c σ y := by
    rw [hc.r_eq]
    exact (Real.exp_pos 1).le.trans exp_le_rFlag
  have hE : 1 ≤ Real.exp (O.met.r c σ y / 2) := Real.one_le_exp (by positivity)
  rw [sub_mulVec, Real.rpow_zero, mul_one]
  refine (norm_sub_le _ _).trans ((add_le_add h5' h6).trans ?_)
  generalize Real.exp (O.met.r c σ y / 2) = E at hE ⊢
  generalize √(P.om c σ ch y ξ.ofLp) = s at h7 ⊢
  have h8 : ‖ξ‖ ≤ s / c₄ := (le_div_iff₀' hc₄).2 h7
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  calc K * E * ‖ξ‖ * ‖v‖ + C₃ * ‖ξ‖ * ‖v‖ ≤ K * E * ‖ξ‖ * ‖v‖ + |C₃| * E * ‖ξ‖ * ‖v‖ := by
        gcongr
        exact (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hE)
    _ = (K + |C₃|) * E * ‖ξ‖ * ‖v‖ := by ring
    _ ≤ (K + |C₃|) * E * (s / c₄) * ‖v‖ := by gcongr
    _ = (K + |C₃|) / c₄ * E * s * ‖v‖ := by ring

end Flag

open GlobalTheory.Toroidal in
theorem _root_.GlobalTheory.T.l2_dbar_local_chart_estimate : Hypotheses2 → HypothesesH → OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (y₀ : GlobalTheory.CxPts (O.var c).str σ), y₀ ∉ offBd O.Φ c σ →
  ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ))
    (Hh H0 : ∀ τ : D.host.E →+* ℂ, ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → Matrix (Fin (O.S.Dw.mult τ)) (Fin (O.S.Dw.mult τ)) ℂ)
    (μ K c₀ C₀ : ℝ), IsOpen U ∧ y₀ ∈ U ∧ U ⊆ ch.e.source ∧ IsOpen (U ∩ offBd O.Φ c σ) ∧ 0 < c₀ ∧ 0 ≤ μ ∧
    ∀ y ∈ U, y ∈ offBd O.Φ c σ →
      (∀ n : Letter O.S.Dw → ℤ, lnRatio (metsOf x O.Φ c none σ n) (refMet x O.Φ c σ n) y =
        (∑ z : Letter O.S.Dw, (n z : ℝ) * (Real.log (grSq (Hh z.1 (ch.e y)) z.2) - Real.log (grSq (H0 z.1 (ch.e y)) z.2))) / 2) ∧
      ∀ τ : D.host.E →+* ℂ, (Hh τ (ch.e y)).PosDef ∧ (H0 τ (ch.e y)).PosDef ∧
        (∀ a b, DifferentiableAt ℝ (fun w => Hh τ w a b) (ch.e y) ∧ DifferentiableAt ℝ (fun w => H0 τ w a b) (ch.e y)) ∧
        (∀ v : Fin (O.S.Dw.mult τ) → ℂ, c₀ * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ H0 τ (ch.e y) *ᵥ v).re ∧
          (star v ⬝ᵥ H0 τ (ch.e y) *ᵥ v).re ≤ C₀ * ‖v‖ ^ 2 ∧
          O.met.r c σ y ^ (-μ) * (star v ⬝ᵥ H0 τ (ch.e y) *ᵥ v).re ≤ (star v ⬝ᵥ Hh τ (ch.e y) *ᵥ v).re ∧
          (star v ⬝ᵥ Hh τ (ch.e y) *ᵥ v).re ≤ O.met.r c σ y ^ μ * (star v ⬝ᵥ H0 τ (ch.e y) *ᵥ v).re) ∧
        ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim, c₀ * ‖ξ‖ ≤ √(P.om c σ ch y ξ.ofLp) ∧ ∀ v : Fin (O.S.Dw.mult τ) → ℂ,
          ‖((H0 τ (ch.e y))⁻¹ * wirt (H0 τ) (ch.e y) ξ) *ᵥ v‖ ≤ C₀ * ‖ξ‖ * ‖v‖ ∧
          ‖((Hh τ (ch.e y))⁻¹ * wirt (Hh τ) (ch.e y) ξ - (H0 τ (ch.e y))⁻¹ * wirt (H0 τ) (ch.e y) ξ) *ᵥ v‖ ≤
            K * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) * ‖v‖ := by
  intro _ _ D O x P hc hf hr c σ y₀ hy₀
  obtain ⟨ch, U, g, hy₀U, hA⟩ := UpperTheory.exists_holomorphic_adapted_chart D O x P hc hf hr c σ y₀
  obtain ⟨V3, c₃, C₃, hV3o, hV3, hV3U, hc₃, h3⟩ := UpperTheory.local_metric_lower_bound D O x P hc hf hr c σ ch U g hA y₀ hy₀U
  obtain ⟨V4, c₄, hV4o, hV4, -, hc₄, h4⟩ := UpperTheory.chart_metric_lower_bound D O x P hc hf hr c σ ch y₀ (hA.2.1 hy₀U)
  obtain ⟨GlobalBoundRefinements, K, μ₆, hV6o, hV6, -, hμ₆, h6⟩ := conn_bound D O x P hc hf hr c σ ch U g hA y₀ hy₀U hy₀
  obtain ⟨μ₁, hμ₁⟩ := ToroidalCompactificationData.exists_isMuExp x
  have hsm := hA.2.2.2.2.2 (x.hodge (embOf O.κ.e σ)) _ (isOpen_not_liesIn (genBd O.s.T.Z)) (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ x _)
  refine ⟨ch, V3 ∩ V4 ∩ GlobalBoundRefinements, GlobalTheory.BdGram.gramIn O (x.hodge _) ch g, GlobalTheory.BdGram.gramIn O (x.eigMet _) ch g,
    max μ₁ μ₆, max K 0, min c₃ c₄, C₃, (hV3o.inter hV4o).inter hV6o, ⟨⟨hV3, hV4⟩, hV6⟩,
    fun y hy => hA.2.1 (hV3U hy.1.1), ?_, lt_min hc₃ hc₄, le_max_of_le_right hμ₆, ?_⟩
  · have e : V3 ∩ V4 ∩ GlobalBoundRefinements ∩ offBd O.Φ c σ = (V3 ∩ V4 ∩ GlobalBoundRefinements) ∩ (U ∩ offBd O.Φ c σ) := by
      ext y
      constructor
      · rintro ⟨hy, hb⟩
        exact ⟨hy, hV3U hy.1.1, hb⟩
      · rintro ⟨hy, -, hb⟩
        exact ⟨hy, hb⟩
    rw [e]
    exact ((hV3o.inter hV4o).inter hV6o).inter hA.2.2.1
  intro y hy hb
  have hyU : y ∈ U := hV3U hy.1.1
  have hys : y ∈ ch.e.source := hA.2.1 hyU
  have hb' : ¬ LiesIn ((O.Φ.C c).down y) (genBd O.s.T.Z) := hb
  have hr1 : 1 ≤ O.met.r c σ y := by
    rw [hc.r_eq]
    exact (Real.one_lt_exp_iff.2 one_pos).le.trans exp_le_rFlag
  have hr0 : 0 < O.met.r c σ y := one_pos.trans_le hr1
  refine ⟨fun n => UpperTheory.log_ratio_metrics_adapted D O x P hc hf hr c σ ch U g hA y hyU n, fun τ => ?_⟩
  have key : ∀ G : EigMet O.s.T.Z (embOf O.κ.e σ), GlobalTheory.BdGram.gramIn O G ch g τ (ch.e y) = G.gram _ (g y) τ := by
    intro G
    unfold GlobalTheory.BdGram.gramIn
    rw [ch.e.left_inv hys]
  have hmem : ch.e y ∈ ch.e '' (U ∩ {p | (O.Φ.C c).down p ∈ {y' | ¬ LiesIn y' (genBd O.s.T.Z)}}) :=
    ⟨y, ⟨hyU, hb'⟩, rfl⟩
  refine ⟨(x.hodge _).pos _ _ _, (x.eigMet _).pos _ _ _, fun a b => ⟨?_, (h3 y hy.1.1 τ).1 a b⟩, fun v => ?_,
    fun ξ => ⟨?_, fun v => ⟨((h3 y hy.1.1 τ).2 v).2.2 ξ, ?_⟩⟩⟩
  · exact (((hsm τ).smooth b a).contDiffAt ((hsm τ).isOpen.mem_nhds hmem)).differentiableAt (by simp)
  · obtain ⟨l3, u3, -⟩ := (h3 y hy.1.1 τ).2 v
    have hn : 0 ≤ (star v ⬝ᵥ GlobalTheory.BdGram.gramIn O (x.eigMet _) ch g τ (ch.e y) *ᵥ v).re :=
      le_trans (mul_nonneg hc₃.le (sq_nonneg _)) l3
    obtain ⟨m1, m2⟩ := hμ₁.2 (embOf O.κ.e σ) ((O.Φ.C c).down y) hb' (g y) τ v
    have er : x.r (embOf O.κ.e σ) ((O.Φ.C c).down y) = O.met.r c σ y := by rw [hc.r_eq]; rfl
    rw [er] at m1 m2
    simp only [key] at hn l3 u3 ⊢
    refine ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)) l3, u3, ?_, ?_⟩
    · refine le_trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hr1 (neg_le_neg (le_max_left _ _))) hn) ?_
      exact m1
    · refine m2.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hr1 (le_max_left _ _)) hn)
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)) (h4 y hy.1.2 ξ)
  · refine (h6 y hy.2 hb τ ξ v).trans ?_
    have h1 : O.met.r c σ y ^ μ₆ ≤ O.met.r c σ y ^ max μ₁ μ₆ :=
      Real.rpow_le_rpow_of_exponent_le hr1 (le_max_right _ _)
    have h0 : 0 ≤ O.met.r c σ y ^ μ₆ := (Real.rpow_pos_of_pos hr0 _).le
    have hR : 0 ≤ Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) * ‖v‖ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (norm_nonneg _)
    have e1 : ∀ k m : ℝ, k * m * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) * ‖v‖ =
        k * m * (Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) * ‖v‖) := fun k m => by ring
    rw [e1, e1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) h1 h0 (le_max_right _ _)) hR
