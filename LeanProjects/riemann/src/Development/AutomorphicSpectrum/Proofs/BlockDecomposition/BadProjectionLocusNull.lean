import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticoneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatioStatement
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCriticalFibreInfinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq.Crit

open Filter Topology
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
open ReciprocityTheory.ChartRestriction.G.Geo (MRing fibreFinite sameOrbit_of_segre mem_mcPts_of_sameOrbit)

section Family

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem exists_injective (hC : CriticalFibreInfinite.Statement) {P : Ideal (MRing ι)}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1))
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ : IsGoodProj P Ψ)
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {V : Set (Fin e → ℂ)} (hV : IsOpen V) (hVne : V.Nonempty)
    (hγ : ∀ y ∈ V, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P)
    (horb : ∀ y ∈ V, ∀ y' ∈ V, SameOrbit (γ y) (γ y') → y = y')
    (h0 : ∀ y ∈ V, Ψ (segre (γ y)) 0 ≠ 0) :
    ∃ y ∈ V, Function.Injective (fderiv ℂ (fun y' => ratio (Ψ (segre (γ y')))) y) := by
  by_contra hall
  push Not at hall
  have : Nonempty K := hP.1
  obtain ⟨t, ht⟩ := hC e e V (fun y' => ratio (Ψ (segre (γ y')))) hV hVne
    (fun y hy => (differentiableAt_ratio Ψ (hγ y hy).1 (h0 y hy)).differentiableWithinAt) hall
  refine (fibreFinite K ι P e Ψ hP hΨ t).not_infinite ?_
  have hinj : Set.InjOn (fun y => (Ψ (segre (γ y)) 0)⁻¹ • segre (γ y))
      {y | y ∈ V ∧ ratio (Ψ (segre (γ y))) = t} := by
    rintro y1 ⟨hy1, -⟩ y2 ⟨hy2, -⟩ h
    refine horb y1 hy1 y2 hy2 (sameOrbit_of_segre (hγ y2 hy2).2.1
      (Ψ (segre (γ y1)) 0 * (Ψ (segre (γ y2)) 0)⁻¹) (mul_ne_zero (h0 y1 hy1) (inv_ne_zero (h0 y2 hy2))) ?_)
    have h' : (Ψ (segre (γ y1)) 0)⁻¹ • segre (γ y1) = (Ψ (segre (γ y2)) 0)⁻¹ • segre (γ y2) := h
    rw [mul_smul, ← h', smul_smul, mul_inv_cancel₀ (h0 y1 hy1), one_smul]
  refine (Set.Infinite.image hinj ht).mono ?_
  rintro _ ⟨y, ⟨hy, hty⟩, rfl⟩
  have := smul_mem_fibre hP.2.1.2.1 (hγ y hy).2 Ψ (h0 y hy)
  rwa [hty] at this

theorem exists_proj_ne_zero (hC : CriticalFibreInfinite.Statement) {P : Ideal (MRing ι)}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1))
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ : IsGoodProj P Ψ)
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {V : Set (Fin e → ℂ)} (hV : IsOpen V)
    (hγ : ∀ y ∈ V, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P)
    (horb : ∀ y ∈ V, ∀ y' ∈ V, SameOrbit (γ y) (γ y') → y = y')
    {y : Fin e → ℂ} (hy : y ∈ V) : ∃ y' ∈ V, Ψ (segre (γ y')) 0 ≠ 0 := by
  by_contra hall
  push Not at hall
  have hne : Ψ (segre (γ y)) ≠ 0 := hΨ _ (hγ y hy).2
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj (hall y hy)
  have hcont : ContinuousOn (fun y' => Ψ (segre (γ y')) j) V := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ (hγ y' hy').1) j).continuousAt.continuousWithinAt
  have hV'o : IsOpen (V ∩ (fun y' => Ψ (segre (γ y')) j) ⁻¹' {0}ᶜ) :=
    hcont.isOpen_inter_preimage hV isOpen_compl_singleton
  have h0' : ∀ y' ∈ V ∩ (fun y' => Ψ (segre (γ y')) j) ⁻¹' {0}ᶜ, swapProj j Ψ (segre (γ y')) 0 ≠ 0 := by
    intro y' hy'
    simpa [swapProj_apply] using hy'.2
  obtain ⟨y1, hy1, hinj⟩ := exists_injective hC hP (isGoodProj_swapProj hΨ j) hV'o ⟨y, hy, hj⟩
    (fun y' hy' => hγ y' hy'.1) (fun a ha b hb => horb a ha.1 b hb.1) h0'
  refine not_injective_of_coord_eventually_const (j.pred hj0) 0
    (differentiableAt_ratio _ (hγ y1 hy1.1).1 (h0' y1 hy1)) ?_ hinj
  filter_upwards [hV'o.mem_nhds hy1] with y' hy'
  simp [PtsSheetOnlyNull.ratio, swapProj_apply, hall y' hy'.1]

end Family

section Chart

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {X : Scheme.{0}} {i : X ⟶ MP ℤ m n} {D : ℕ}

theorem isMultiHomog_coord (q : Σ k, Bk n k) :
    IsMultiHomog (MvPolynomial.X q : Pol n) (Pi.single q.1 1) := by
  classical
  intro d hd k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hd
  subst hd
  obtain ⟨k0, i0⟩ := q
  by_cases h : k = k0
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j, (Finsupp.single (⟨k0, i0⟩ : Σ k, Bk n k) 1 : (Σ k, Bk n k) →₀ ℕ) ⟨k, j⟩ = 0 := by
      intro j
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact h (congrArg Sigma.fst e).symm
    simp [this, h]

theorem ev_coord (p : ∀ k, Bk n k) {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀}
    (hy : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)) {z : (Σ k, Bk n k) → ℂ} (hz : Over i y z)
    (q : Σ k, Bk n k) :
    ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) (i.app _ (dehomog p (MvPolynomial.X q))) y =
      z q / z ⟨q.1, p q.1⟩ := by
  classical
  have hw : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart p) :=
    CxPts.mem_ptsIn.2 (CxPts.mem_ptsIn.1 hy)
  rw [CxPts.ev_app i rfl, GlobalTheory.T.dehomogenized_eval_eq_ratio m n p _ _ (isMultiHomog_coord q) _ z hz hw]
  simp [Pi.single_apply, Finset.prod_ite_eq']

variable [IsIntegral X] [IsClosedImmersion i]

theorem exists_lift (hPh : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (ptIdeal (i (genericPoint X))))
    (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} :
    ∃ (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ), IsOpen O ∧
      (y ∈ c.e.source → c.finChart y ∈ O) ∧ O ⊆ c.finChart.target ∧ DifferentiableOn ℂ γ O ∧
      ∀ v ∈ O, Over i (c.finChart.symm v) (γ v) ∧ γ v ∈ mcPts (ptIdeal (i (genericPoint X))) := by
  obtain ⟨z, hzP, hz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
  choose p hp using hzP.1
  have hyW : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => CxPts.mem_ptsIn.1 ((hz k (p k)).1.2 (hp k)))
  set W := i ⁻¹ᵁ mchart p with hW
  refine ⟨c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W,
    fun v q => ev (i ≫ mpStr ℤ m n) σ₀ W (i.app _ (dehomog p (MvPolynomial.X q))) (c.finChart.symm v),
    c.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn W), fun hys => ?_, Set.inter_subset_left, ?_, ?_⟩
  · refine ⟨c.finChart.map_source hys, ?_⟩
    rw [Set.mem_preimage, c.finChart.left_inv hys]
    exact hyW
  · refine differentiableOn_pi.2 fun q => ?_
    exact ((c.analyticOnNhd_finChart_iff (isOpen_ptsIn W) _).2 (c.holo W _)).differentiableOn
  · rintro v ⟨-, hvW⟩
    obtain ⟨z', hz'P, hz'⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i (c.finChart.symm v)
    have hne : ∀ k, z' ⟨k, p k⟩ ≠ 0 := fun k => (hz' k (p k)).1.1 (by
      refine CxPts.mem_ptsIn.2 ?_
      exact Set.mem_iInter.1 (CxPts.mem_ptsIn.1 hvW) k)
    have hso : SameOrbit (fun q => ev (i ≫ mpStr ℤ m n) σ₀ W (i.app _ (dehomog p (MvPolynomial.X q)))
        (c.finChart.symm v)) z' := by
      refine ⟨fun k => (z' ⟨k, p k⟩)⁻¹, fun k => inv_ne_zero (hne k), ?_⟩
      funext q
      rw [ev_coord p hvW hz' q, div_eq_inv_mul]
    exact ⟨GlobalTheory.T.isUnder_of_same_orbit m n _ _ _ hz' hso, mem_mcPts_of_sameOrbit hPh hso hz'P⟩

end Chart

theorem over_liftOf {m : ℕ} {n : Fin (m + 1) → ℕ} {X : Scheme.{0}} {i : X ⟶ MP ℤ m n}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (h : Over i y z) : Over i y (liftOf i y) := by
  have hex : ∃ z, Over i y z := ⟨z, h⟩
  unfold liftOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem volume_chart_crit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ),
    GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D → ∀ Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D,
      IsGoodProj (ptIdeal (i (genericPoint X))) Ψ → ∀ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D,
        volume (c.e.target ∩ c.e.symm ⁻¹' {y | (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 = 0) ∨
          ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  intro m n X _ i _ D hX Ψ hΨ c
  obtain ⟨-, hp₃, hp₄, -⟩ := GlobalTheory.T.mixed_cycle_point_dictionary m n X i (D + 1) hX.dim_eq
  have hP := hp₄ (hp₃.2 hX.charZero)
  have hPh := hP.2.1.2.1
  have hCF := CriticalFibreInfinite.proof
  have horb : ∀ (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ), O ⊆ c.finChart.target →
      (∀ v ∈ O, Over i (c.finChart.symm v) (γ v)) → ∀ v ∈ O, ∀ v' ∈ O, SameOrbit (γ v) (γ v') → v = v' := by
    intro O γ hO hγ v hv v' hv' h
    have e := (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ (hγ v hv) (hγ v' hv')).2 h
    calc v = c.finChart (c.finChart.symm v) := (c.finChart.right_inv (hO hv)).symm
      _ = c.finChart (c.finChart.symm v') := congrArg _ e
      _ = v' := c.finChart.right_inv (hO hv')
  have hlift : ∀ v ∈ c.finChart.target, ∃ (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ), IsOpen O ∧
      v ∈ O ∧ O ⊆ c.finChart.target ∧ DifferentiableOn ℂ γ O ∧
      ∀ v ∈ O, Over i (c.finChart.symm v) (γ v) ∧ γ v ∈ mcPts (ptIdeal (i (genericPoint X))) := by
    intro v hvT
    obtain ⟨O, γ, hOo, hvO, hOT, hγd, hγ⟩ := exists_lift (y := c.finChart.symm v) hPh c
    refine ⟨O, γ, hOo, ?_, hOT, hγd, hγ⟩
    have := hvO (c.finChart.map_target hvT)
    rwa [c.finChart.right_inv hvT] at this
  have hS1 : volume {v | v ∈ c.finChart.target ∧ ∃ z, Over i (c.finChart.symm v) z ∧ Ψ (segre z) 0 = 0} = 0 := by
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro v ⟨hvT, -⟩
    obtain ⟨O, γ, hOo, hvO, hOT, hγd, hγ⟩ := hlift v hvT
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hOo v hvO
    have hdiff : ∀ w ∈ O, DifferentiableAt ℂ γ w := fun w hw => (hγd w hw).differentiableAt (hOo.mem_nhds hw)
    refine ⟨Metric.ball v r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball v r).isPreconnected,
      fun w => Ψ (segre (γ w)) 0, ?_, ?_, ?_⟩
    · have hd : DifferentiableOn ℂ (fun w => Ψ (segre (γ w)) 0) O := fun w hw =>
        (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ (hdiff w hw)) 0).differentiableWithinAt
      exact ((SCV.analyticOnNhd_iff_differentiableOn hOo).2 hd).mono hball
    · exact exists_proj_ne_zero hCF hP hΨ Metric.isOpen_ball
        (fun w hw => ⟨hdiff w (hball hw), (hγ w (hball hw)).2⟩)
        (fun a ha b hb => horb O γ hOT (fun u hu => (hγ u hu).1) a (hball ha) b (hball hb))
        (Metric.mem_ball_self hr)
    · rintro w ⟨⟨-, z', hz', h0'⟩, hw⟩
      obtain ⟨a, ha, e⟩ := (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ hz' (hγ w (hball hw)).1).1 rfl
      rw [segre_orbit e, map_smul, Pi.smul_apply, smul_eq_mul] at h0'
      exact (mul_eq_zero.1 h0').resolve_left (Finset.prod_ne_zero_iff.2 fun k _ => ha k)
  have hS2 : volume {v | v ∈ c.finChart.target ∧ (∀ z, Over i (c.finChart.symm v) z → Ψ (segre z) 0 ≠ 0) ∧
      ¬ IsRegAt i Ψ c (c.finChart.symm v)} = 0 := by
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro v ⟨hvT, hnz, -⟩
    obtain ⟨O, γ, hOo, hvO, hOT, hγd, hγ⟩ := hlift v hvT
    have hdiff : ∀ w ∈ O, DifferentiableAt ℂ γ w := fun w hw => (hγd w hw).differentiableAt (hOo.mem_nhds hw)
    have hcont : ContinuousOn (fun w => Ψ (segre (γ w)) 0) O := fun w hw =>
      (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ (hdiff w hw)) 0).continuousAt.continuousWithinAt
    have hO'o : IsOpen (O ∩ (fun w => Ψ (segre (γ w)) 0) ⁻¹' {0}ᶜ) :=
      hcont.isOpen_inter_preimage hOo isOpen_compl_singleton
    have hτd : DifferentiableOn ℂ (fun w => PtsSheetOnlyNull.ratio (Ψ (segre (γ w))))
        (O ∩ (fun w => Ψ (segre (γ w)) 0) ⁻¹' {0}ᶜ) := fun w hw =>
      (differentiableAt_ratio Ψ (hdiff w hw.1) hw.2).differentiableWithinAt
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO'o v ⟨hvO, hnz _ (hγ v hvO).1⟩
    refine ⟨Metric.ball v r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball v r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun w => PtsSheetOnlyNull.ratio (Ψ (segre (γ w)))) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC hO'o hτd).mono hball, ?_, ?_⟩
    · obtain ⟨y1, hy1, hinj⟩ := exists_injective hCF hP hΨ Metric.isOpen_ball ⟨v, Metric.mem_ball_self hr⟩
        (fun w hw => ⟨hdiff w (hball hw).1, (hγ w (hball hw).1).2⟩)
        (fun a ha b hb => horb O γ hOT (fun u hu => (hγ u hu).1) a (hball ha).1 b (hball hb).1)
        (fun w hw => (hball hw).2)
      refine ⟨y1, hy1, ?_⟩
      show (ReciprocityTheory.AnForm.A.jacC _ y1).det ≠ 0
      rw [ReciprocityTheory.AnForm.A.det_jacC]
      exact (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
    · rintro w ⟨⟨hwT, -, hnr⟩, hw⟩
      show (ReciprocityTheory.AnForm.A.jacC _ w).det = 0
      rw [ReciprocityTheory.AnForm.A.det_jacC]
      have hev : projCoord i Ψ ∘ c.finChart.symm =ᶠ[𝓝 w]
          fun w => PtsSheetOnlyNull.ratio (Ψ (segre (γ w))) := by
        filter_upwards [hO'o.mem_nhds (hball hw)] with u hu
        have hso := (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ (over_liftOf (hγ u hu.1).1) (hγ u hu.1).1).1 rfl
        exact ratios_eq_of_sameOrbit Ψ hso hu.2
      unfold IsRegAt at hnr
      rw [not_not, c.finChart.right_inv hwT, hev.fderiv_eq] at hnr
      exact hnr
  have key : volume (c.finChart.target ∩ c.finChart.symm ⁻¹' {y | (∃ z, Over i y z ∧ Ψ (segre z) 0 = 0) ∨
      ¬ IsRegAt i Ψ c y}) = 0 := by
    refine measure_mono_null ?_ (measure_union_null hS1 hS2)
    rintro v ⟨hvT, hvB⟩
    by_cases h : ∃ z, Over i (c.finChart.symm v) z ∧ Ψ (segre z) 0 = 0
    · exact Or.inl ⟨hvT, h⟩
    · exact Or.inr ⟨hvT, fun z hz h0 => h ⟨z, hz, h0⟩, hvB.resolve_left h⟩
  rw [← (GlobalTheory.FinChart.measurePreserving_toV (D := D)).measure_preimage_emb
    (GlobalTheory.FinChart.toV D).toHomeomorph.measurableEmbedding]
  exact key

end GlobalTheory.CompanionTheory.MixZ.ArchEq.Crit
