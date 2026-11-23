import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHolomorphicMorseInequalityUniformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasIntegralEqChartDensityIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVolumeDensityFiniteIsOpenPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChartStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.Morse

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem cmb_eq_frame (P : Pair p) (m : ℕ) {ι : Type} [Fintype ι] (f : ι → X.functionField)
    (hf : ∀ l, f l ∈ P.H m 1) (c : ι → ℂ) (σ : k →+* ℂ) (y : CxPts p σ) (i : P.L.B.ι) (j : P.A.B.ι)
    (hi : y ∈ ptsIn p σ (P.L.B.U i)) (hj : y ∈ ptsIn p σ (P.A.B.U j)) :
    cmb (vals P m 1 f) c σ y = ‖∑ l, c l * ratVal (P.loc m 1 (f l) i j) y‖ ^ 2 *
      Real.exp (-((m : ℝ) * (P.L.φ σ).φ i y)) * Real.exp (-(P.A.φ σ).φ j y) := by
  obtain ⟨θ, hθ, h⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P m 1 σ y i j hi hj
  have e : ∑ l, c l * vals P m 1 f σ y l = θ * ((∑ l, c l * ratVal (P.loc m 1 (f l) i j) y) *
      (Real.exp (-(((m : ℤ) : ℝ) * (P.L.φ σ).φ i y + ((1 : ℤ) : ℝ) * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
    simp only [vals, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h _ (hf l)]
    ring
  rw [cmb, e, norm_mul, hθ, one_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    mul_pow, sq (Real.exp _), ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem continuous_cmb {D : ℕ} (hX : IsArithVar p D) (P : Pair p) (m : ℕ) {ι : Type} [Fintype ι]
    (f : ι → X.functionField) (hf : ∀ l, f l ∈ P.H m 1) (c : ι → ℂ) (σ : k →+* ℂ) :
    Continuous fun y => cmb (vals P m 1 f) c σ y := by
  have hp := (GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P m 1).1 σ
  have e : (fun y => cmb (vals P m 1 f) c σ y) = fun y =>
      (∑ a, ∑ b, c a * (starRingEnd ℂ) (c b) *
        (val P m 1 σ y (f a) * (starRingEnd ℂ) (val P m 1 σ y (f b)))).re := by
    funext y
    rw [cmb, ← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum,
      Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [vals, map_mul]
    ring
  rw [e]
  exact Complex.continuous_re.comp (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
    continuous_const.mul (hp _ (hf a) _ (hf b)))

theorem integral_over_chart_le_l2 {D : ℕ} (hX : IsArithVar p D) (hs : GenSmooth p D) (P : Pair p) (m : ℕ) {ι : Type}
    [Fintype ι] (f : ι → X.functionField) (hf : ∀ l, f l ∈ P.H m 1) (c : ι → ℂ) (ω : ∀ σ, VolDens p σ D)
    (σ : k →+* ℂ) (C : AlgChart p σ D) (T : Set (ReciprocityTheory.L2DbarEstimates.V D)) (hT : IsOpen T) (hTt : T ⊆ C.e.target) :
    ∫ v in T, cmb (vals P m 1 f) c σ (C.e.symm v) * (ω σ).dens C (C.e.symm v) ≤
      l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  haveI := hX.compactSpace σ
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  obtain ⟨hfin, -⟩ := GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hs σ (ω σ)
  have hcont := continuous_cmb hX P m f hf c σ
  set S := C.e.source ∩ C.e ⁻¹' T with hSdef
  have hSo : IsOpen S := C.e.isOpen_inter_preimage hT
  have hSs : S ⊆ C.e.source := Set.inter_subset_left
  have hST : C.e '' S = T := by
    rw [hSdef, C.e.image_source_inter_eq']
    ext v
    refine ⟨fun hv => ?_, fun hv => ⟨hTt hv, ?_⟩⟩
    · have h := hv.2
      simp only [Set.mem_preimage, C.e.right_inv hv.1] at h
      exact h
    · simp only [Set.mem_preimage, C.e.right_inv (hTt hv)]
      exact hv
  have h1 := (GlobalTheory.T.meas_integral_eq_chartDensity_integral k X p D hX σ (ω σ) C S _ hSo.measurableSet hSs hcont).2
  rw [hST] at h1
  rw [← h1]
  have hnn : ∀ σ' (y : CxPts p σ'), 0 ≤ cmb (vals P m 1 f) c σ' y := fun _ _ => by unfold cmb; positivity
  have hint : Integrable (fun y => cmb (vals P m 1 f) c σ y) (ω σ).meas :=
    integrableOn_univ.1 (hcont.continuousOn.integrableOn_compact isCompact_univ)
  calc ∫ y in S, cmb (vals P m 1 f) c σ y ∂(ω σ).meas ≤ ∫ y, cmb (vals P m 1 f) c σ y ∂(ω σ).meas :=
        setIntegral_le_integral hint (Eventually.of_forall (hnn σ))
    _ ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
        unfold l2
        exact single_le_finsum (f := fun σ' => ∫ y, cmb (vals P m 1 f) c σ' y ∂(ω σ').meas) σ (Set.toFinite _)
          fun σ' => integral_nonneg (hnn σ')

theorem local_bound {D : ℕ} (hX : IsArithVar p D) (hs : GenSmooth p D) (P : Pair p) (hP : P.L.SemiPos D)
    (ω : ∀ σ, VolDens p σ D) (ρ : ∀ σ, CxPts p σ → ℝ) (hρ : ∀ σ, (ω σ).IsRatio (P.L.φ σ) (ρ σ)) (ε : ℝ)
    (hε : 0 < ε) (σ : k →+* ℂ) (y₀ : CxPts p σ) :
    ∃ N ∈ 𝓝 y₀, ∀ᶠ m : ℕ in atTop, ∀ (ι : Type) [Fintype ι] (f : ι → X.functionField),
      (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ), ∀ y ∈ N,
        cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  obtain ⟨R⟩ := hs σ
  obtain ⟨a, ha⟩ := R.cover y₀
  set C := R.chart a with hC
  set i := pick (P.L.φ σ).isLB y₀ with hi
  set j := pick (P.A.φ σ).isLB y₀ with hj
  set O := C.e.source ∩ ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j) with hOdef
  have hO : IsOpen O := (C.e.open_source.inter (isOpen_ptsIn _)).inter (isOpen_ptsIn _)
  have hy₀O : y₀ ∈ O := ⟨⟨ha, mem_pick _ _⟩, mem_pick _ _⟩
  set U := C.e '' O with hUdef
  have hU : IsOpen U := C.e.isOpen_image_of_subset_source hO fun y hy => hy.1.1
  have hUO : ∀ v ∈ U, C.e.symm v ∈ O ∧ v ∈ C.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨by rwa [C.e.left_inv hy.1.1], C.e.map_source hy.1.1⟩
  obtain ⟨r, hr, hrU⟩ : ∃ r > 0, Metric.closedBall (C.e y₀) r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds ⟨y₀, hy₀O, rfl⟩)
  set K := Metric.closedBall (C.e y₀) r with hK
  have hsymm : ContinuousOn C.e.symm U := C.e.continuousOn_symm.mono fun v hv => (hUO v hv).2
  have hdc : ContinuousOn (fun v => (ω σ).dens C (C.e.symm v)) U :=
    ((ω σ).cont C).comp hsymm fun v hv => (hUO v hv).1.1.1
  have hψc : ContinuousOn (fun v => (P.A.φ σ).φ j (C.e.symm v)) U :=
    ContinuousOn.comp (show ContinuousOn ((P.A.φ σ).φ j) (ptsIn p σ (P.A.B.U j)) from
      fun y hy => ((P.A.cInf σ) j y hy).continuousAt.continuousWithinAt) hsymm fun v hv => (hUO v hv).1.2
  have hφ' : ContDiffOn ℝ 2 (fun v => (P.L.φ σ).φ i (C.e.symm v)) U := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((P.L.cInf σ).contDiffAt C hy.1.1 hy.1.2).contDiffWithinAt
  have hlevi : ∀ z ∈ U, ∀ ξ : Fin D → ℂ,
      0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (((P.L.φ σ).φ i (C.e.symm v) : ℝ) : ℂ)) z ξ).re := by
    rintro _ ⟨y, hy, rfl⟩ ξ
    exact hP σ i C y ⟨hy.1.1, hy.1.2⟩ ξ
  have hgc : ContinuousOn (fun v => Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v)) U :=
    (Real.continuous_exp.comp_continuousOn hψc.neg).mul hdc
  have hgp : ∀ v ∈ U, 0 < Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v) := fun v hv =>
    mul_pos (Real.exp_pos _) ((ω σ).pos C _ (hUO v hv).1.1.1)
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_closedBall (C.e y₀) r).exists_isMinOn
    ⟨C.e y₀, Metric.mem_closedBall_self hr.le⟩ (hdc.mono hrU)
  have hd₀ : 0 < (ω σ).dens C (C.e.symm v₀) := (ω σ).pos C _ (hUO v₀ (hrU hv₀)).1.1.1
  obtain ⟨δ, hδ, hball, hev⟩ := GlobalTheory.T.local_holomorphic_morse_inequality_uniform D U K (fun v => (P.L.φ σ).φ i (C.e.symm v))
    (fun v => Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v))
    (ε * (ω σ).dens C (C.e.symm v₀)) hU (isCompact_closedBall _ _) hrU hφ' hlevi hgc hgp (mul_pos hε hd₀)
  refine ⟨C.e.source ∩ C.e ⁻¹' K, inter_mem (C.e.open_source.mem_nhds ha)
    ((C.e.continuousAt ha).preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr)), ?_⟩
  filter_upwards [hev] with m hm ι _ f hf c y hy
  have hyO : y ∈ O := by
    have := (hUO (C.e y) (hrU hy.2)).1
    rwa [C.e.left_inv hy.1] at this
  set F : ReciprocityTheory.L2DbarEstimates.V D → ℂ := fun v => ∑ l, c l * ratVal (P.loc m 1 (f l) i j) (C.e.symm v) with hF
  have hFd : DifferentiableOn ℂ F U := by
    refine DifferentiableOn.fun_sum (𝕜 := ℂ) (u := Finset.univ)
      (A := fun l v => c l * ratVal (P.loc m 1 (f l) i j) (C.e.symm v)) fun l _ => ?_
    exact (((GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P m 1 σ (f l) (hf l) i j).2 D C).mono fun v hv =>
      ⟨(hUO v hv).2, (hUO v hv).1.1.2, (hUO v hv).1.2⟩).const_mul (c l)
  have hid : ∀ v ∈ U, ‖F v‖ ^ 2 * Real.exp (-((m : ℝ) * (P.L.φ σ).φ i (C.e.symm v))) *
      (Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v)) =
      cmb (vals P m 1 f) c σ (C.e.symm v) * (ω σ).dens C (C.e.symm v) := by
    intro v hv
    rw [cmb_eq_frame P m f hf c σ _ i j (hUO v hv).1.1.2 (hUO v hv).1.2]
    ring
  have hBU : ∀ w ∈ Metric.ball (C.e y) δ, w ∈ U := fun w hw =>
    hball _ hy.2 (Metric.ball_subset_closedBall hw)
  have hI : ∫ w in Metric.ball (C.e y) δ, ‖F w‖ ^ 2 * Real.exp (-((m : ℝ) * (P.L.φ σ).φ i (C.e.symm w))) *
      (Real.exp (-(P.A.φ σ).φ j (C.e.symm w)) * (ω σ).dens C (C.e.symm w)) =
      ∫ w in Metric.ball (C.e y) δ, cmb (vals P m 1 f) c σ (C.e.symm w) * (ω σ).dens C (C.e.symm w) :=
    setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun w hw => hid w (hBU w hw)
  have hle := integral_over_chart_le_l2 hX hs P m f hf c ω σ C _ Metric.isOpen_ball fun w hw => (hUO w (hBU w hw)).2
  have hInn : 0 ≤ ∫ w in Metric.ball (C.e y) δ, cmb (vals P m 1 f) c σ (C.e.symm w) * (ω σ).dens C (C.e.symm w) :=
    setIntegral_nonneg Metric.isOpen_ball.measurableSet fun w hw =>
      mul_nonneg (by unfold cmb; positivity) ((ω σ).pos C _ (hUO w (hBU w hw)).1.1.1).le
  have hdy : 0 < (ω σ).dens C y := (ω σ).pos C y hy.1
  have hρ0 : 0 ≤ ρ σ y := by
    have h2 := C.chernDens_nonneg (P.L.cInf σ) (hP σ) hy.1
    rw [(hρ σ).2 C y hy.1] at h2
    exact (mul_nonneg_iff_of_pos_right hdy).1 h2
  have hdet : (ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((P.L.φ σ).φ i (C.e.symm v) : ℝ) : ℂ)) (C.e y)).det.re /
      Real.pi ^ D = ρ σ y * (ω σ).dens C y / D.factorial := by
    have h1 := (hρ σ).2 C y hy.1
    rw [C.chernDens_eq (P.L.cInf σ) hy.1 hyO.1.2] at h1
    have hpi : 0 < Real.pi ^ D := by positivity
    have hfac : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
    rw [div_eq_div_iff hpi.ne' hfac.ne', ← h1]
    simp only [AlgChart.hess]
    field_simp
  have h0 := hm (C.e y) hy.2 F hFd
  beta_reduce at h0
  rw [hid _ (hrU hy.2), hI, hdet, C.e.left_inv hy.1] at h0
  have hmin' : (ω σ).dens C (C.e.symm v₀) ≤ (ω σ).dens C y := by
    have := hmin hy.2
    simp only [Set.mem_setOf_eq, C.e.left_inv hy.1] at this
    exact this
  set I := ∫ w in Metric.ball (C.e y) δ, cmb (vals P m 1 f) c σ (C.e.symm w) * (ω σ).dens C (C.e.symm w)
  have hM : 0 ≤ (m : ℝ) ^ D * I := mul_nonneg (by positivity) hInn
  have h3 : (ω σ).dens C y * cmb (vals P m 1 f) c σ y ≤
      (ω σ).dens C y * ((ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * I) := by
    rw [mul_comm]
    refine h0.trans ?_
    calc (ρ σ y * (ω σ).dens C y / D.factorial + ε * (ω σ).dens C (C.e.symm v₀)) * (m : ℝ) ^ D * I
        = (ρ σ y * (ω σ).dens C y / D.factorial + ε * (ω σ).dens C (C.e.symm v₀)) * ((m : ℝ) ^ D * I) := by ring
      _ ≤ (ρ σ y * (ω σ).dens C y / D.factorial + ε * (ω σ).dens C y) * ((m : ℝ) ^ D * I) := by gcongr
      _ = (ω σ).dens C y * ((ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * I) := by ring
  refine (le_of_mul_le_mul_left h3 hdy).trans (mul_le_mul_of_nonneg_left hle ?_)
  positivity

theorem cmb_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (ρ : ∀ σ, CxPts p σ → ℝ),
    (∀ σ, (ω σ).IsRatio (P.L.φ σ) (ρ σ)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ (ι : Type) [Fintype ι]
    (f : ι → X.functionField), (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ) (σ : k →+* ℂ) (y : CxPts p σ),
    cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  intro k _ X _ p D hX hs P hP ω ρ hρ ε hε
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  choose N hN hev using fun σ (y₀ : CxPts p σ) => local_bound hX hs P hP ω ρ hρ ε hε σ y₀
  have hcov : ∀ σ : k →+* ℂ, ∃ t : Finset (CxPts p σ), ∀ y, ∃ y₀ ∈ t, y ∈ N σ y₀ := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨t, -, ht⟩ := (isCompact_univ (X := CxPts p σ)).elim_nhds_subcover (N σ) fun y _ => hN σ y
    exact ⟨t, fun y => by simpa using ht (Set.mem_univ y)⟩
  choose t ht using hcov
  have hall : ∀ᶠ m : ℕ in atTop, ∀ σ : k →+* ℂ, ∀ y₀ ∈ t σ, ∀ (ι : Type) [Fintype ι] (f : ι → X.functionField),
      (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ), ∀ y ∈ N σ y₀,
        cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c :=
    eventually_all.2 fun σ => (eventually_all_finset (t σ)).2 fun y₀ _ => hev σ y₀
  filter_upwards [hall] with m hm ι _ f hf c σ y
  obtain ⟨y₀, hy₀, hy⟩ := ht σ y
  exact hm σ y₀ hy₀ ι f hf c y hy

end GlobalTheory.HSAmp.Morse
