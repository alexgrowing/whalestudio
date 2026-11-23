import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioSameDivisorMultiplicitiesStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot

open MvPolynomial MeasureTheory Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blockNorm (k : K) (z : (Σ k, ι k) → ℂ) : ℝ := Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2)

theorem blockNorm_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (k : K) :
    blockNorm k (fun p => c p.1 * z p) = ‖c k‖ * blockNorm k z := by
  unfold blockNorm
  simp only [norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem sum_sq_pos {z : (Σ k, ι k) → ℂ} {k : K} (hz : ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hz
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩

def blockSet (ι : K → Type) [∀ k, Fintype (ι k)] : Set ((Σ k, ι k) → ℂ) :=
  {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

theorem smul_mem_blockSet {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} :
    (fun p => c p.1 * z p) ∈ blockSet ι ↔ z ∈ blockSet ι := by
  simp only [blockSet, mem_setOf_eq, ne_eq, mul_eq_zero, not_or]
  exact forall_congr' fun k => exists_congr fun i => ⟨fun h => h.2, fun h => ⟨hc k, h⟩⟩

def fsOfDeg (γ : K → ℕ) : HermLine ι where
  a k := γ k
  h := (blockSet ι).indicator fun z => ∏ k, blockNorm k z ^ γ k
  pos z hz := by
    rw [indicator_of_mem (show z ∈ blockSet ι from hz)]
    exact Finset.prod_pos fun k _ => pow_pos (Real.sqrt_pos.mpr (sum_sq_pos (hz k))) _
  smul c z hc := by
    by_cases hz : z ∈ blockSet ι
    · rw [indicator_of_mem ((smul_mem_blockSet hc).mpr hz), indicator_of_mem hz,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [blockNorm_smul, mul_pow, zpow_natCast]
    · rw [indicator_of_notMem (fun h => hz ((smul_mem_blockSet hc).mp h)), indicator_of_notMem hz,
        mul_zero]

theorem fsOfDeg_h_of_notMem (γ : K → ℕ) {z : (Σ k, ι k) → ℂ} (hz : z ∉ blockSet ι) :
    (fsOfDeg γ : HermLine ι).h z = 0 :=
  show (blockSet ι).indicator (fun z : (Σ k, ι k) → ℂ => ∏ k, blockNorm k z ^ γ k) z = 0 from
    indicator_of_notMem hz _

theorem isSmoothHerm_fsOfDeg (γ : K → ℕ) : IsSmoothHerm (fsOfDeg γ : HermLine ι) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => ∏ k, blockNorm k z ^ γ k)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    refine contDiffOn_prod fun k _ => ContDiffOn.pow ?_ _
    refine ContDiffOn.sqrt ?_ fun z hz => (sum_sq_pos (hz k)).ne'
    refine ContDiff.contDiffOn ?_
    refine ContDiff.sum fun i _ => ?_
    exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ _)
  exact h1.congr fun z hz =>
    show (blockSet ι).indicator (fun z : (Σ k, ι k) → ℂ => ∏ k, blockNorm k z ^ γ k) z = _ from
      indicator_of_mem (show z ∈ blockSet ι from hz) _

theorem hermLine_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp_all

def twist (M A B : HermLine ι) : HermLine ι := (M.tensor A).tensor B.inv

theorem twist_tensor {M : HermLine ι} (hM : ∀ z, z ∉ blockSet ι → M.h z = 0) (A B : HermLine ι) :
    (twist M A B).tensor B = M.tensor A := by
  refine hermLine_ext ?_ ?_
  · funext k
    simp [twist, HermLine.tensor, HermLine.inv]
  · funext z
    show M.h z * A.h z * (B.h z)⁻¹ * B.h z = M.h z * A.h z
    by_cases hz : z ∈ blockSet ι
    · have := (B.pos z hz).ne'
      field_simp
    · simp [hM z hz]

theorem isSmoothHerm_twist {M A B : HermLine ι} (hM : IsSmoothHerm M) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) : IsSmoothHerm (twist M A B) :=
  isSmoothHerm_tensor (isSmoothHerm_tensor hM hA) (isSmoothHerm_inv hB)

theorem mInt_congr_null {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) {g g' : X → ℝ}
    (h : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | g x ≠ g' x}) = 0) :
    mInt A Φ g = mInt A Φ g' := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae ?_
    refine (ae_restrict_iff' (A.chart j).open_target.measurableSet).mpr ?_
    refine ae_iff.mpr (measure_mono_null (fun y hy => ?_) (h j))
    simp only [mem_setOf_eq, Classical.not_imp] at hy
    refine ⟨hy.1, fun he => hy.2 ?_⟩
    have he' : g ((A.chart j).symm y) = g' ((A.chart j).symm y) := he
    rw [he']
  · rfl

section Zeros

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem evC_zero_iff (R : AnLogRes P J e) {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    {x y : R.X} (hy : y ∈ R.U x) :
    evC (R.lift y y) s = 0 ↔ evC (R.lift x y) s = 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have h := eval_bsmul_of_isMultiHomog hs c (R.lift x y)
  have hp : ∏ k, c k ^ a k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have h' : evC (R.lift y y) s = (∏ k, c k ^ a k) * evC (R.lift x y) s := by
    rw [hzc]
    exact h
  rw [h']
  simp [hp]

theorem mem_mcPts_span {s : MRing ι} {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (h0 : evC z s = 0) : z ∈ mcPts (Ideal.span {s}) := by
  refine ⟨hz, fun f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  have h0' : eval z (map (Int.castRingHom ℂ) s) = 0 := h0
  simp [h0']

theorem not_flat_form (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {s : MRing ι} {a : K → ℕ}
    (hs : IsMultiHomog s a) (hsP : s ∉ P) (j : Fin R.A.n) {O : Set (Fin e → ℂ)}
    (hO : IsOpen O) (hOt : O ⊆ (R.A.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, evC (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u)) s = 0) : False := by
  have hJh : IsMultiHomogIdeal (Ideal.span {s}) :=
    ⟨{s}, fun f hf => ⟨a, by rw [mem_singleton_iff.mp hf]; exact hs⟩, rfl⟩
  have hJP : ¬ Ideal.span {s} ≤ P := fun h => hsP ((Ideal.span_singleton_le_iff_mem _).mp h)
  have hN := projB_null Ψ hP hΨ hJh hJP

  obtain ⟨u1, hu1O, hu1⟩ : ∃ u ∈ O, (R.A.chart j).symm u ∉ brBad R Ψ := by
    by_contra hall
    push Not at hall
    obtain ⟨u, hu⟩ := hne
    have hpos := IsOpen.measure_pos volume hO ⟨u, hu⟩
    have hsub : O ⊆ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ :=
      fun v hv => ⟨hOt hv, hall v hv⟩
    exact hpos.ne' (measure_mono_null hsub (brBad_null R Ψ hP hΨ j))
  have hu1t := hOt hu1O
  set x1 := (R.A.chart j).symm u1 with hx1
  have hchart : R.A.chart j x1 = u1 := (R.A.chart j).right_inv hu1t
  obtain ⟨hQa, hQd⟩ := brGood R Ψ x1 hu1 j ((R.A.chart j).map_target hu1t)
  rw [hchart] at hQa hQd
  set Q := brQ R Ψ ∘ (R.A.chart j).symm with hQ
  have hsurj : LinearMap.range (fderiv ℂ Q u1 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = ⊤ := by
    have hu : IsUnit (fderiv ℂ Q u1 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) :=
      (LinearMap.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hQd)
    exact LinearMap.range_eq_top.mpr ((Module.End.isUnit_iff _).mp hu).2
  have hmap : map Q (𝓝 u1) = 𝓝 (Q u1) := hQa.hasStrictFDerivAt.map_nhds_eq_of_surj hsurj

  have hV : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x1 ∈ 𝓝 u1 :=
    ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x1)).mem_nhds ⟨hu1t, R.mem_U x1⟩
  have hG : ContinuousAt (fun u => Ψ (segre (R.lift x1 ((R.A.chart j).symm u))) 0) u1 :=
    (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ x1 j ⟨hu1t, R.mem_U x1⟩) 0).continuousAt
  have hG0 : Ψ (segre (R.lift x1 x1)) 0 ≠ 0 := projection_zero_ne_of_notMem_bridgeBadSet R Ψ hu1
  have hev : ∀ᶠ u in 𝓝 u1, Q u ∈ {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts (Ideal.span {s}) ∧
      Ψ (segre z) = Fin.cons 1 y} := by
    filter_upwards [hV, hG.eventually_ne hG0, hO.mem_nhds hu1O] with u huV hune huO
    set x := (R.A.chart j).symm u with hx
    have hx0 : Ψ (segre (R.lift x x)) 0 ≠ 0 := by
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R huV.2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hune
    obtain ⟨z, hz, hzw, hzΨ⟩ := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 hx0
    refine ⟨z, hz, ?_, ?_⟩
    · have hmem := R.mem x x (R.mem_U x)
      have hl : R.lift x x ∈ mcPts (Ideal.span {s}) := mem_mcPts_span hmem.1 (h0 u huO)
      refine mem_mcPts_of_sameOrbit hJh (sameOrbit_of_segre hmem.1 (Ψ (segre (R.lift x x)) 0)⁻¹
        (inv_ne_zero hx0) hzw) hl
    · rw [hzw]
      exact hzΨ
  have hmem : {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts (Ideal.span {s}) ∧
      Ψ (segre z) = Fin.cons 1 y} ∈ 𝓝 (Q u1) := by
    rw [← hmap]
    exact hev
  exact (Measure.measure_pos_of_mem_nhds volume hmem).ne' hN

theorem zeros_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {s : MRing ι} {a : K → ℕ}
    (hs : IsMultiHomog s a) (hsP : s ∉ P) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | evC (R.lift x x) s = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0 with hx0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set F : (Fin e → ℂ) → ℂ := fun u => evC (R.lift x0 ((R.A.chart j).symm u)) s with hF
  have hFa : AnalyticOnNhd ℂ F V := fun u hu =>
    analyticAt_eval_poly _ fun p => analyticAt_pi_iff.mp (analyticAt_lift_chart R x0 j hu) p
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, F, hFa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat_form R Ψ hP hΨ hs hsP j Metric.isOpen_ball (fun u hu => (hball hu).1)
      ⟨u0, Metric.mem_ball_self hr⟩ fun u hu => (evC_zero_iff R hs (hball hu).2).mpr (hall u hu)
  · rintro w ⟨⟨-, hw0⟩, hwB⟩
    exact (evC_zero_iff R hs (hball hwB).2).mp hw0

end Zeros

section Main

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem arInt_eq_mInt (hB : ResBridgeStatement) (hG : GoodProjExistsStatement) (R : AnLogRes P J e)
    {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P (e + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    arInt P s A L = mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  have hex := hG K ι P e hP
  unfold arInt ptsIntegral
  rw [dif_pos hex]
  exact hB K ι P J e R _ L A s hP hex.choose_spec hL hA hs

theorem logNorm_sub_eq {M A B : HermLine ι} {f g : MRing ι} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ blockSet ι) (hf : evC z f ≠ 0) (hg : evC z g ≠ 0) :
    logNorm (twist M A B) f z - logNorm M g z =
      Real.log (‖evC z f‖ / ‖evC z g‖ * B.h z / A.h z) := by
  have hM := M.pos z hz
  have hA := A.pos z hz
  have hB := B.pos z hz
  have hf' : 0 < ‖evC z f‖ := norm_pos_iff.mpr hf
  have hg' : 0 < ‖evC z g‖ := norm_pos_iff.mpr hg
  have e1 : logNorm (twist M A B) f z = Real.log (‖evC z f‖ / (M.h z * A.h z * (B.h z)⁻¹)) := rfl
  have e2 : logNorm M g z = Real.log (‖evC z g‖ / M.h z) := rfl
  rw [e1, e2, ← Real.log_div (by positivity) (by positivity)]
  congr 1
  field_simp

end Main

theorem inter_sub_eq_neg_mInt : RatRStatement → ResBridgeStatement → GoodProjExistsStatement →
    AvoidStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (L : Fin e → HermLine ι)
      (A B : HermLine ι) (f g : MRing ι) (w : ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (e + 1) →
      (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → IsLineIso P A.a B.a f g →
      IsDefectOn P (mcPts P) f g A B w →
      I P (e + 1) (Fin.snoc L A) - I P (e + 1) (Fin.snoc L B) =
        -mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) := by
  intro _ hBr hG _ K _ ι _ I hI P J e R L A B f g w hP hL hA hB hIso hw
  obtain ⟨⟨α, γ, hfα, hgγ, hdeg⟩, hU⟩ := hIso
  have hfP : f ∉ P := hU.1
  have hgP : g ∉ P := hU.2.1
  set M' : HermLine ι := fsOfDeg γ with hM'def
  set M : HermLine ι := twist M' A B with hMdef
  have hM' : IsSmoothHerm M' := isSmoothHerm_fsOfDeg γ
  have hM : IsSmoothHerm M := isSmoothHerm_twist hM' hA hB
  have hMa : ∀ k, M.a k = α k := by
    intro k
    have h := hdeg k
    have e1 : M.a k = (γ k : ℤ) + A.a k + -B.a k := rfl
    rw [e1]
    linarith
  have hM'a : ∀ k, M'.a k = γ k := fun _ => rfl

  have a1 := hI.2.1 P e L M B hP hL hM hB
  have a2 := hI.2.1 P e L M' A hP hL hM' hA
  have ht : M.tensor B = M'.tensor A := twist_tensor (fun z hz => fsOfDeg_h_of_notMem γ hz) A B
  rw [ht] at a1

  have r1 := hI.2.2 P e L M f α hP hL hM hMa hfα hfP
  have r2 := hI.2.2 P e L M' g γ hP hL hM' hM'a hgγ hgP
  rw [recR_eq] at r1 r2

  have hc := GlobalTheory.T.unit_ratio_same_divisor_multiplicities K ι P f g hU
  have hcyc : cycR I P L f = cycR I P L g := by
    unfold cycR
    refine finsum_mem_congr hc.1 fun W hW => ?_
    rw [hc.2 W (hc.1 ▸ hW)]

  have hsf : IsSectionOn P M f := ⟨α, hMa, hfα, hfP⟩
  have hsg : IsSectionOn P M' g := ⟨γ, hM'a, hgγ, hgP⟩
  rw [arInt_eq_mInt hBr hG R hP hL hM hsf] at r1
  rw [arInt_eq_mInt hBr hG R hP hL hM' hsg] at r2
  have hpot : ∀ i, IsPotential R.A (potOf R (L i)) := fun i => potOf_isPotential R (L i) (hL i)
  have hlin := mIntLinear R.A (fun j => potOf R (L j)) hpot (-1)
    (fun x => logNorm M' g (R.lift x x)) (fun x => logNorm M f (R.lift x x))
    (brIntegrable R L M' g hP hL hM' hsg) (brIntegrable R L M f hP hL hM hsf)
  obtain ⟨Ψ, hΨ⟩ := hG K ι P e hP
  have hw' : mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) =
      mInt R.A (fun j => potOf R (L j))
        (fun x => -1 * logNorm M' g (R.lift x x) + logNorm M f (R.lift x x)) := by
    refine mInt_congr_null _ _ fun j => ?_
    refine measure_mono_null ?_ (measure_union_null (zeros_null R Ψ hP hΨ hfα hfP j)
      (zeros_null R Ψ hP hΨ hgγ hgP j))
    rintro y ⟨hyt, hy⟩
    by_contra hcon
    have hnf : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) f ≠ 0 :=
      fun h => hcon (Or.inl ⟨hyt, h⟩)
    have hng : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) g ≠ 0 :=
      fun h => hcon (Or.inr ⟨hyt, h⟩)
    have hmem := R.mem ((R.A.chart j).symm y) _ (R.mem_U ((R.A.chart j).symm y))
    apply hy
    have hd := hw _ hmem g f (by rw [mul_comm, sub_self]; exact P.zero_mem) hng
    have := logNorm_sub_eq (M := M') (A := A) (B := B) (show _ ∈ blockSet ι from hmem.1) hnf hng
    show w _ = -1 * logNorm M' g _ + logNorm M f _
    rw [hd, ← this]
    ring
  rw [hw', hlin]
  linarith

end GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot
