import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.BStepA
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

theorem bsB_holo_ratio (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {la : La} {a b : ι → Y → ℂ}
    (ha : A.IsSecOn la (A.Mset w0 s De) a) (hb : A.IsSecOn la (A.Mset w0 s De) b)
    (hb0 : ∀ y ∈ A.Mset w0 s De, b (A.pick y) y ≠ 0) :
    Holo n (flatStein A hD hF).z
      (fun y : A.Mset w0 s De => a (A.pick (y : Y)) y / b (A.pick (y : Y)) y) := by
  rw [holo_flat_iff A hD hF (fun y => a (A.pick y) y / b (A.pick y) y)]
  intro i
  have hne : ∀ v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De,
      (b i ∘ (A.chart i).symm) v ≠ 0 := fun v hv =>
    bsA_ne_of_tr A hb.2 hv.2 ((A.chart i).map_target hv.1) (A.mem_pick _) (hb0 _ hv.2)
  have h3 := (ha.1 i).mul ((hb.1 i).inv hne)
  refine h3.congr fun v hv => ?_
  simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply]
  rw [← div_eq_mul_inv]
  exact bsA_tr_ratio A ha.2 hb.2 hv.2 (A.mem_pick _) ((A.chart i).map_target hv.1)

theorem bsB_z_ne {x : Y} (hx : x ∈ A.Mset w0 s De) {i0 : Fin n}
    (hX : MvPolynomial.X i0 ∣ De) : A.zmap w0 s x i0 ≠ 0 := by
  obtain ⟨Q, hQ⟩ := hX
  intro h0
  apply hx.2
  rw [hQ, MvPolynomial.eval_mul, MvPolynomial.eval_X, h0, zero_mul]

theorem bsB_lambda (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hLSE : LSEAll.{u} n) :
    SmoothR n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      Real.log (∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2)) ∧
    LeviNonneg n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      Real.log (∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2)) := by
  have hg : ∀ k, Holo n (flatStein A hD hF).z
      (fun y : A.Mset w0 s De => w k (A.pick (y : Y)) y / w0 (A.pick (y : Y)) y) := fun k =>
    bsB_holo_ratio A hD hF (bsA_isSecOn_mono A (hD.sec_w k) (Set.subset_univ _))
      (bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ _)) fun y hy => hy.1
  have hpos : ∀ x : A.Mset w0 s De, 0 < ∑ i : Fin 0, Real.exp ((Fin.elim0 i : A.Mset w0 s De → ℝ) x) +
      ∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2 := by
    intro x
    obtain ⟨k, hk⟩ := hD.no_common_zero x
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ k))
    have : w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x ≠ 0 := div_ne_zero hk x.2.1
    positivity
  have h := hLSE (A.Mset w0 s De) (flatStein A hD hF).z (flatStein A hD hF).isLocalHomeomorph 0 N
    (fun i => Fin.elim0 i) (fun k y => w k (A.pick (y : Y)) y / w0 (A.pick (y : Y)) y)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hg hpos
  simpa using h

section Psi

variable {mu0 : La} {σ : ι → Y → ℂ}

def bsPsi (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (mu0 : La)
    (σ : ι → Y → ℂ) (y : Y) : ℝ :=
  -Real.log (A.nsq mu0 σ y) - A.ph A.kap (A.pick y) y +
    Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2)

def bsPsiC (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (mu0 : La)
    (σ : ι → Y → ℂ) (i : ι) (y : Y) : ℝ :=
  A.ph (mu0 - A.kap) i y + Real.log (‖(σ i y)⁻¹‖ ^ 2) +
    Real.log (‖(jz A w0 s i y).det‖ ^ 2)

theorem bsB_logsq {f : V n → ℂ} {p : V n} {O : Set (V n)} (hO : IsOpen O) (hp : p ∈ O)
    (hf : DifferentiableOn ℂ f O) (hne : f p ≠ 0) :
    ContDiffAt ℝ ∞ (fun v => Real.log (‖f v‖ ^ 2)) p := by
  have h1 : ContDiffAt ℂ ∞ f p :=
    (contDiffOn_of_differentiableOn n f O hO hf p hp).contDiffAt (hO.mem_nhds hp)
  have h2 : ContDiffAt ℝ ∞ (fun v => ‖f v‖ ^ 2) p := (h1.restrict_scalars ℝ).norm_sq ℂ
  exact h2.log (by positivity)

theorem bsB_psi_chart (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {y : Y} (hy : y ∈ A.Mset w0 s De) {i : ι}
    (hi : y ∈ (A.chart i).source) : bsPsi A w0 s mu0 σ y = bsPsiC A w0 s mu0 σ i y := by
  have hp := A.mem_pick y
  have hσi : σ i y ≠ 0 := bsA_ne_of_tr A hσ.1.2 hy hi hp (hσ.2 y hy)
  have hg : A.g A.kap (A.pick y) i y ≠ 0 := A.g_ne _ _ _ y hp hi
  have hdet : (jz A w0 s i y).det ≠ 0 := jz_det_ne A hD hF y hy i hi
  unfold bsPsi bsPsiC
  rw [bsA_nsq_chart A hσ.1.2 hy hi, jz_det_trans A hD hF y hy (A.pick y) i hp hi,
    bsA_ph_sub A mu0 A.kap hi, A.ph_trans A.kap (A.pick y) i y hp hi]
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, norm_mul, mul_pow,
    Real.log_mul (by positivity) (by positivity), norm_inv, inv_pow, Real.log_inv]
  ring

theorem bsB_O_open (hD : A.D0 L w w0 s) (i : ι) :
    IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) :=
  (A.chart i).isOpen_inter_preimage_symm (isOpen_Mset A hD)

theorem bsB_O_mem {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι} (hi : x ∈ (A.chart i).source) :
    A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De :=
  ⟨(A.chart i).map_source hi, by simpa [(A.chart i).left_inv hi] using hx⟩

theorem bsB_jz_eq {i : ι} {v : V n} (hv : v ∈ (A.chart i).target) :
    jz A w0 s i ((A.chart i).symm v) = fderiv ℂ (A.zLoc w0 s i) v := by
  unfold jz; rw [(A.chart i).right_inv hv]

theorem bsB_det_diff (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {x : Y}
    (hx : x ∈ A.Mset w0 s De) {i : ι} (hi : x ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x),
      DifferentiableAt ℂ ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) v := by
  filter_upwards [differentiableAt_det_jz A hD hF x hx i hi,
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)] with v h1 h2
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(A.chart i).open_target.mem_nhds h2] with v' hv'
  simp [bsB_jz_eq A hv']

theorem bsB_inv_diffOn (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (i : ι) :
    DifferentiableOn ℂ ((fun y => (σ i y)⁻¹) ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by
  have h := (hσ.1.1 i).inv (fun v hv =>
    bsA_ne_of_tr A hσ.1.2 hv.2 ((A.chart i).map_target hv.1) (A.mem_pick _) (hσ.2 _ hv.2))
  exact h.congr fun v _ => rfl

theorem bsB_psiC_smooth (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (A.ph (mu0 - A.kap) i ∘ (A.chart i).symm) (A.chart i x) ∧
    ContDiffAt ℝ ∞ ((fun y => Real.log (‖(σ i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm) (A.chart i x) ∧
    ContDiffAt ℝ ∞ ((fun y => Real.log (‖(jz A w0 s i y).det‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i x) := by
  have hO := bsB_O_open A (De := De) hD i
  have hxO := bsB_O_mem A hx hi
  refine ⟨(A.smooth_ph _ i).contDiffAt ((A.chart i).open_target.mem_nhds hxO.1), ?_, ?_⟩
  · have hne : ((fun y => (σ i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
      exact inv_ne_zero (bsA_ne_of_tr A hσ.1.2 hx hi (A.mem_pick x) (hσ.2 x hx))
    exact bsB_logsq hO hxO (bsB_inv_diffOn A hσ i) hne
  · have hc : ContDiffAt ℂ ∞ ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) (A.chart i x) := by
      refine (contDiffAt_det_jz A hD hF x hx i hi).congr_of_eventuallyEq ?_
      filter_upwards [(A.chart i).open_target.mem_nhds hxO.1] with v hv
      simp [bsB_jz_eq A hv]
    have h2 : ContDiffAt ℝ ∞ (fun v => ‖((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) v‖ ^ 2)
        (A.chart i x) := (hc.restrict_scalars ℝ).norm_sq ℂ
    have hne : ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
      exact jz_det_ne A hD hF x hx i hi
    exact h2.log (by positivity)

end Psi

section Ph0

variable {mu0 : La} {σ : ι → Y → ℂ}

theorem bsB_psi_evEq (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) : bsPsi A w0 s mu0 σ =ᶠ[𝓝 x] bsPsiC A w0 s mu0 σ i := by
  filter_upwards [(isOpen_Mset A hD).mem_nhds hx, (A.chart i).open_source.mem_nhds hi]
    with y h1 h2
  exact bsB_psi_chart A hD hF hσ h1 h2

theorem bsB_psi_smoothAt (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (bsPsi A w0 s mu0 σ ∘ (A.chart i).symm) (A.chart i x) := by
  obtain ⟨h1, h2, h3⟩ := bsB_psiC_smooth A hD hF hσ hx hi
  have hC : ContDiffAt ℝ ∞ (bsPsiC A w0 s mu0 σ i ∘ (A.chart i).symm) (A.chart i x) :=
    (h1.add h2).add h3
  refine hC.congr_of_eventuallyEq ?_
  have ht : Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have := (A.chart i).continuousAt_symm ((A.chart i).map_source hi)
    rwa [ContinuousAt, (A.chart i).left_inv hi] at this
  exact (bsB_psi_evEq A hD hF hσ hx hi).comp_tendsto ht

theorem bsB_psi_levi (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0))
    {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι} (hi : x ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    0 ≤ A.leviAt i (bsPsi A w0 s mu0 σ) x ξ := by
  obtain ⟨h1, h2, h3⟩ := bsB_psiC_smooth A hD hF hσ hx hi
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hO := bsB_O_open A (De := De) hD i
  have hxO := bsB_O_mem A hx hi
  rw [leviAt_congr A i _ _ x hi (bsB_psi_evEq A hD hF hσ hx hi)]
  have e1 : bsPsiC A w0 s mu0 σ i = fun y => (fun y => A.ph (mu0 - A.kap) i y +
      Real.log (‖(σ i y)⁻¹‖ ^ 2)) y + Real.log (‖(jz A w0 s i y).det‖ ^ 2) := rfl
  have E1 := leviAt_add A i (fun y => A.ph (mu0 - A.kap) i y + Real.log (‖(σ i y)⁻¹‖ ^ 2))
    (fun y => Real.log (‖(jz A w0 s i y).det‖ ^ 2)) x ((h1.add h2).of_le hle) (h3.of_le hle) ξ
  have E2 := leviAt_add A i (A.ph (mu0 - A.kap) i) (fun y => Real.log (‖(σ i y)⁻¹‖ ^ 2)) x
    (h1.of_le hle) (h2.of_le hle) ξ
  have hσx : σ i x ≠ 0 := bsA_ne_of_tr A hσ.1.2 hx hi (A.mem_pick x) (hσ.2 x hx)
  have E3 := leviAt_log_normSq A i (fun y => (σ i y)⁻¹) x hi (by
      filter_upwards [hO.mem_nhds hxO] with v hv
      exact (bsB_inv_diffOn A hσ i).differentiableAt (hO.mem_nhds hv)) (inv_ne_zero hσx) ξ
  have E4 := leviAt_log_normSq A i (fun y => (jz A w0 s i y).det) x hi (bsB_det_diff A hD hF hx hi)
      (jz_det_ne A hD hF x hx i hi) ξ
  have E5 := hpos i x hi ξ
  simp only [add_zero] at E5
  rw [e1]
  beta_reduce at E1 E2 E3 E4 ⊢
  linarith

def bsPh0 (A : WeightedAtlas n Y ι La) (w : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (mu0 : La) (σ : ι → Y → ℂ) (y : Y) : ℝ :=
  bsPsi A w0 s mu0 σ y + 1 / 2 * Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2)

theorem smooth_leviNonneg_frameWeight (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hLSE : LSEAll.{u} n)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0)) :
    SmoothR n (flatStein A hD hF).z (fun x : A.Mset w0 s De => bsPh0 A w w0 s mu0 σ x) ∧
    LeviNonneg n (flatStein A hD hF).z (fun x : A.Mset w0 s De => bsPh0 A w w0 s mu0 σ x) := by
  obtain ⟨hΛs, hΛl⟩ := bsB_lambda A hD hF hLSE
  have hΨs : SmoothR n (flatStein A hD hF).z (fun x : A.Mset w0 s De => bsPsi A w0 s mu0 σ x) :=
    smoothR_flat A hD hF _ fun x hx =>
      ⟨A.pick x, A.mem_pick x, bsB_psi_smoothAt A hD hF hσ hx (A.mem_pick x)⟩
  have hΨl : LeviNonneg n (flatStein A hD hF).z
      (fun x : A.Mset w0 s De => bsPsi A w0 s mu0 σ x) :=
    leviNonneg_flat A hD hF _ fun x hx =>
      ⟨A.pick x, A.mem_pick x, bsB_psi_smoothAt A hD hF hσ hx (A.mem_pick x),
        bsB_psi_levi A hD hF hσ hpos hx (A.mem_pick x)⟩
  have hcs : SmoothR n (flatStein A hD hF).z (fun _ : A.Mset w0 s De => (1 / 2 : ℝ)) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.const n _ ((1 / 2 : ℝ) : ℂ)
  have hHs := SmoothR.mul n _ _ _ hcs hΛs
  refine ⟨SmoothR.add n _ _ _ hΨs hHs, fun x ξ => ?_⟩
  have e := levi_add n (flatStein A hD hF).z _ _ (SmoothR.ckR n _ 2 _ hΨs)
    (SmoothR.ckR n _ 2 _ hHs) x ξ
  have e2 := levi_const_mul n (flatStein A hD hF).z (1 / 2) _ (SmoothR.ckR n _ 2 _ hΛs) x ξ
  unfold bsPh0
  rw [e, Complex.add_re, e2, Complex.re_ofReal_mul]
  have h1 := hΨl x ξ
  have h2 := hΛl x ξ
  positivity

end Ph0

end

end ReciprocityTheory.L2DbarEstimates.Y
