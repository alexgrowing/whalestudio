import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.IsOpenKappaOpenNeighbourhood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart

open Matrix

noncomputable section

theorem unitPolydisc_eq_ball (n : ℕ) :
    GroundTheory.Heights₂.Heights.unitPolydisc n = Metric.ball (0 : Fin n → ℂ) 1 := by
  ext z
  simp [GroundTheory.Heights₂.Heights.unitPolydisc, Metric.mem_ball, dist_zero_right,
    pi_norm_lt_iff one_pos]

theorem cuspTime_eq_logWeight {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) :
    GroundTheory.Heights₂.Heights.cuspTime h z j = lwP₂ (z (Fin.castLE h j)) := by
  simp only [GroundTheory.Heights₂.Heights.cuspTime, GroundTheory.Heights₂.Heights.cuspCoord, lwP₂, one_div]
  ring

theorem puncturedChart_eq_punctured {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) :
    GroundTheory.Heights₂.Heights.puncturedChart h U = punctured h U := rfl

theorem chartImag_eq_chartY {n a g : ℕ} (h : a ≤ n)
    (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (z : Fin n → ℂ) : GroundTheory.Heights₂.Heights.chartImag h τ0 B z = chartY h τ0 B z := by
  simp only [GroundTheory.Heights₂.Heights.chartImag, chartY, imPart, cuspTime_eq_logWeight]

theorem chartRadius_eq_chartR {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) :
    GroundTheory.Heights₂.Heights.chartRadius h z = chartR h z := by
  simp only [GroundTheory.Heights₂.Heights.chartRadius, GroundTheory.Heights₂.Heights.cuspCoord, chartR, one_div]

theorem hermPair_inv_eq_realIP {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (v w : Fin g → ℂ) :
    GroundTheory.Heights₂.Heights.hermPair Y⁻¹ v w = realIP Y v w := rfl

theorem hermValue_eq_qf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w : ι → ℂ) :
    GroundTheory.Heights₂.Heights.hermValue A w = qf A w := rfl

theorem metricLength_eq_yNorm {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℂ) :
    GroundTheory.Heights₂.Heights.metricLength Y w = yNorm Y w := rfl

theorem logDetGram_eq_gramLogDet {g k : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ)
    (F : Matrix (Fin g) (Fin k) ℂ) : GroundTheory.Heights₂.Heights.logDetGram Y F = gramLogDet Y F := rfl

theorem splitCoord_eq_splitPt (n m : ℕ) : GroundTheory.Heights₂.Heights.splitCoord n m = splitPt := rfl

namespace PeriodChartData

def ofBundled (D : GroundTheory.Heights₂.Heights.PeriodChartData) :
    PeriodChartData D.n D.a D.g D.m D.rk where
  U := D.U
  isOpen_U := D.isOpen_U
  U_sub := by rw [← unitPolydisc_eq_ball]; exact D.U_subset
  a_le := D.a_le
  tau0 := D.τ0
  tau_analyticOn := D.τ0_analytic
  tau_transpose_eq := D.τ0_symm
  B := D.B
  B_psd := D.B_psd
  c := D.c
  c_pos := D.c_pos
  Y_ge := fun z hz => by rw [← chartImag_eq_chartY]; exact D.Y_ge z hz
  V := D.V
  isOpen_V := D.isOpen_V
  f := D.f
  f_analytic := D.f_analytic
  f_rank := D.f_rank
  K := D.K
  K_compact := D.isCompact_K
  K_sub := D.K_subset

def bundle {n a g m k : ℕ} (D : PeriodChartData n a g m k) :
    GroundTheory.Heights₂.Heights.PeriodChartData where
  n := n
  m := m
  g := g
  a := a
  rk := k
  a_le := D.a_le
  U := D.U
  isOpen_U := D.isOpen_U
  U_subset := by rw [unitPolydisc_eq_ball]; exact D.U_sub
  τ0 := D.tau0
  τ0_analytic := D.tau_analyticOn
  τ0_symm := D.tau_transpose_eq
  B := D.B
  B_psd := D.B_psd
  c := D.c
  c_pos := D.c_pos
  Y_ge := fun z hz => by rw [chartImag_eq_chartY]; exact D.Y_ge z hz
  V := D.V
  isOpen_V := D.isOpen_V
  f := D.f
  f_analytic := D.f_analytic
  f_rank := D.f_rank
  K := D.K
  isCompact_K := D.K_compact
  K_subset := D.K_sub

section ofBundled

variable (D : GroundTheory.Heights₂.Heights.PeriodChartData)

@[simp] theorem ofBundled_U : (ofBundled D).U = D.U := rfl
@[simp] theorem periodChartData_ofBundled_tau : (ofBundled D).tau0 = D.τ0 := rfl
@[simp] theorem ofBundled_B : (ofBundled D).B = D.B := rfl
@[simp] theorem ofBundled_c : (ofBundled D).c = D.c := rfl
@[simp] theorem ofBundled_V : (ofBundled D).V = D.V := rfl
@[simp] theorem ofBundled_f : (ofBundled D).f = D.f := rfl
@[simp] theorem ofBundled_K : (ofBundled D).K = D.K := rfl

theorem Ustar_ofBundled : (ofBundled D).Ustar = D.Ustar := rfl

theorem Y_ofBundled (z : Fin D.n → ℂ) : (ofBundled D).Y z = D.Y z :=
  (chartImag_eq_chartY _ _ _ _).symm

theorem r_ofBundled (z : Fin D.n → ℂ) : (ofBundled D).r z = D.radius z :=
  (chartRadius_eq_chartR _ _).symm

theorem u_ofBundled (p : (Fin D.n → ℂ) × (Fin D.m → ℂ)) : (ofBundled D).u p = D.u p := by
  show gramLogDet ((ofBundled D).Y p.1) (D.f p) =
    GroundTheory.Heights₂.Heights.logDetGram (D.Y p.1) (D.f p)
  rw [Y_ofBundled]
  rfl

theorem tau_ofBundled (ℓ : Fin D.a → ℂ) (z : Fin D.n → ℂ) :
    (ofBundled D).tau ℓ z = D.period z ℓ := rfl

end ofBundled

section bundle

variable {n a g m k : ℕ} (D : PeriodChartData n a g m k)

@[simp] theorem bundle_n : D.bundle.n = n := rfl
@[simp] theorem bundle_a : D.bundle.a = a := rfl
@[simp] theorem bundle_g : D.bundle.g = g := rfl
@[simp] theorem bundle_m : D.bundle.m = m := rfl
@[simp] theorem bundle_rk : D.bundle.rk = k := rfl
theorem bundle_U : D.bundle.U = D.U := rfl
theorem bundle_τ0 : D.bundle.τ0 = D.tau0 := rfl
theorem bundle_B : D.bundle.B = D.B := rfl
theorem bundle_c : D.bundle.c = D.c := rfl
theorem bundle_V : D.bundle.V = D.V := rfl
theorem bundle_f : D.bundle.f = D.f := rfl
theorem bundle_K : D.bundle.K = D.K := rfl

theorem bundle_Ustar : D.bundle.Ustar = D.Ustar := rfl

theorem bundle_Y (z : Fin n → ℂ) : D.bundle.Y z = D.Y z := chartImag_eq_chartY _ _ _ _

theorem bundle_radius (z : Fin n → ℂ) : D.bundle.radius z = D.r z := chartRadius_eq_chartR _ _

theorem bundle_u (p : (Fin n → ℂ) × (Fin m → ℂ)) : D.bundle.u p = D.u p := by
  show GroundTheory.Heights₂.Heights.logDetGram (D.bundle.Y p.1) (D.f p) = gramLogDet (D.Y p.1) (D.f p)
  rw [bundle_Y]
  rfl

theorem bundle_period (z : Fin n → ℂ) (ℓ : Fin a → ℂ) : D.bundle.period z ℓ = D.tau ℓ z := rfl

theorem ofBundled_bundle : ofBundled D.bundle = D := rfl

end bundle

theorem bundle_ofBundled (D : GroundTheory.Heights₂.Heights.PeriodChartData) : (ofBundled D).bundle = D := by
  cases D
  rfl

def equiv : GroundTheory.Heights₂.Heights.PeriodChartData ≃ Σ n a g m k : ℕ, PeriodChartData n a g m k where
  toFun D := ⟨D.n, D.a, D.g, D.m, D.rk, ofBundled D⟩
  invFun E := E.2.2.2.2.2.bundle
  left_inv D := bundle_ofBundled D
  right_inv := by rintro ⟨n, a, g, m, k, E⟩; rfl

end PeriodChartData

namespace ToricBlock

theorem ofBundled {D : GroundTheory.Heights₂.Heights.PeriodChartData} (T : GroundTheory.Heights₂.Heights.ToricBlock D) :
    ToricBlock (PeriodChartData.ofBundled D) T.r where
  r_le := T.r_le
  B_support := T.support
  sum_posDef := T.pos

def toBundled {D : GroundTheory.Heights₂.Heights.PeriodChartData} {r : ℕ}
    (T : ToricBlock (PeriodChartData.ofBundled D) r) : GroundTheory.Heights₂.Heights.ToricBlock D where
  r := r
  r_le := T.r_le
  support := T.B_support
  pos := T.sum_posDef

theorem toBundled_r {D : GroundTheory.Heights₂.Heights.PeriodChartData} {r : ℕ}
    (T : ToricBlock (PeriodChartData.ofBundled D) r) : (toBundled T).r = r := rfl

def equiv (D : GroundTheory.Heights₂.Heights.PeriodChartData) :
    GroundTheory.Heights₂.Heights.ToricBlock D ≃ {r : ℕ // ToricBlock (PeriodChartData.ofBundled D) r} where
  toFun T := ⟨T.r, ofBundled T⟩
  invFun T := toBundled T.2
  left_inv T := by cases T; rfl
  right_inv T := rfl

theorem iff_bundle {n a g m k : ℕ} (E : PeriodChartData n a g m k) (r : ℕ) :
    ToricBlock E r ↔ ∃ T : GroundTheory.Heights₂.Heights.ToricBlock E.bundle, T.r = r :=
  ⟨fun h => ⟨toBundled (D := E.bundle) h, rfl⟩, by rintro ⟨T, rfl⟩; exact ofBundled T⟩

end ToricBlock

namespace PshData

def ofSiegelFamily {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k) : PshData N g k where
  W := S.W
  isOpen_kappaOpenNeighbourhood := S.isOpen_kappaOpenNeighbourhood
  tau := S.τ
  tau_analytic := S.τ_analytic
  tau_symm := S.τ_symm
  im_posDef := S.im_posDef
  F := S.f
  F_analytic := S.f_analytic
  F_rank := S.f_rank

def toSiegelFamily {N g k : ℕ} (P : PshData N g k) : GroundTheory.Heights₂.Heights.SiegelFamily N g k where
  W := P.W
  isOpen_kappaOpenNeighbourhood := P.isOpen_kappaOpenNeighbourhood
  τ := P.tau
  τ_analytic := P.tau_analytic
  τ_symm := P.tau_symm
  im_posDef := P.im_posDef
  f := P.F
  f_analytic := P.F_analytic
  f_rank := P.F_rank

def equiv (N g k : ℕ) : GroundTheory.Heights₂.Heights.SiegelFamily N g k ≃ PshData N g k where
  toFun := ofSiegelFamily
  invFun := toSiegelFamily
  left_inv S := by cases S; rfl
  right_inv P := by cases P; rfl

theorem ofSiegelFamily_alt {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k) :
    (ofSiegelFamily S).W = S.W := rfl
theorem ofSiegelFamily_tau {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k) :
    (ofSiegelFamily S).tau = S.τ := rfl
theorem ofSiegelFamily_F {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k) :
    (ofSiegelFamily S).F = S.f := rfl

theorem gramLogDet_ofSiegelFamily {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k)
    (x : Fin N → ℂ) :
    gramLogDet (imPart ((ofSiegelFamily S).tau x)) ((ofSiegelFamily S).F x) =
      GroundTheory.Heights₂.Heights.logDetGram ((S.τ x).map Complex.im) (S.f x) := rfl

end PshData

theorem intVecC_zero {g : ℕ} : GroundTheory.Heights₂.Heights.intVecC (0 : Fin g → ℤ) = 0 := by
  ext k; simp [GroundTheory.Heights₂.Heights.intVecC]

theorem intVecC_add {g : ℕ} (a b : Fin g → ℤ) :
    GroundTheory.Heights₂.Heights.intVecC (a + b) =
      GroundTheory.Heights₂.Heights.intVecC a + GroundTheory.Heights₂.Heights.intVecC b := by
  ext k; simp [GroundTheory.Heights₂.Heights.intVecC]

theorem intVecC_smul {g : ℕ} (c : ℤ) (a : Fin g → ℤ) :
    GroundTheory.Heights₂.Heights.intVecC (c • a) = c • GroundTheory.Heights₂.Heights.intVecC a := by
  ext k; simp [GroundTheory.Heights₂.Heights.intVecC]

theorem intVecC_single {g : ℕ} (j : Fin g) :
    GroundTheory.Heights₂.Heights.intVecC (Pi.single j 1) = (Pi.single j (1 : ℂ) : Fin g → ℂ) := by
  ext k
  by_cases h : k = j
  · subst h; simp [GroundTheory.Heights₂.Heights.intVecC]
  · simp [GroundTheory.Heights₂.Heights.intVecC, h]

theorem intVecC_eq_sum {g : ℕ} (a : Fin g → ℤ) :
    GroundTheory.Heights₂.Heights.intVecC a = ∑ j, a j • (Pi.single j (1 : ℂ) : Fin g → ℂ) := by
  ext k
  simp [GroundTheory.Heights₂.Heights.intVecC, Finset.sum_apply, Pi.single_apply]

theorem periodLattice_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) :
    GroundTheory.Heights₂.Heights.periodLattice τ = (periodLattice τ : Set (Fin g → ℂ)) := by
  ext w
  constructor
  · rintro ⟨a, n, rfl⟩
    rw [SetLike.mem_coe, intVecC_eq_sum, intVecC_eq_sum, Matrix.mulVec_sum]
    refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl ⟨j, rfl⟩))) (Submodule.sum_mem _ fun j _ => ?_)
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
  · intro hw
    rw [SetLike.mem_coe, periodLattice] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact ⟨Pi.single j 1, 0, by rw [intVecC_single, intVecC_zero, mulVec_zero, add_zero]⟩
      · exact ⟨0, Pi.single j 1, by rw [intVecC_single, intVecC_zero, zero_add]⟩
    | zero => exact ⟨0, 0, by rw [intVecC_zero, mulVec_zero, add_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, n, rfl⟩ := hx
      obtain ⟨a', n', rfl⟩ := hy
      exact ⟨a + a', n + n', by rw [intVecC_add, intVecC_add, mulVec_add]; abel⟩
    | smul c x _ hx =>
      obtain ⟨a, n, rfl⟩ := hx
      exact ⟨c • a, c • n, by rw [intVecC_smul, intVecC_smul, mulVec_smul, smul_add]⟩

theorem leadingLattice_eq_firstBlock {g r : ℕ} (hr : r ≤ g) :
    GroundTheory.Heights₂.Heights.leadingLattice g r = (firstBlock hr : Set (Fin g → ℂ)) := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [intVecC_eq_sum, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k.val < r
    · obtain ⟨j, rfl⟩ : ∃ j : Fin r, Fin.castLE hr j = k := ⟨⟨k, hk⟩, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [ha k (not_lt.mp hk), zero_smul]
      exact zero_mem _
  · intro hw
    rw [SetLike.mem_coe, firstBlock] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      refine ⟨Pi.single (Fin.castLE hr j) 1, fun k hk => Pi.single_eq_of_ne ?_ _,
        (intVecC_single _).symm⟩
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castLE] at this
      omega
    | zero => exact ⟨0, fun _ _ => rfl, intVecC_zero.symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨a', ha', rfl⟩ := hy
      exact ⟨a + a', fun k hk => by simp [ha k hk, ha' k hk], (intVecC_add a a').symm⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨c • a, fun k hk => by simp [ha k hk], (intVecC_smul c a).symm⟩

def realIPForm {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (realIP Y)
    (fun v v' w => by simp [realIP, star_add, add_dotProduct])
    (fun c v w => by simp [realIP, star_smul, smul_dotProduct])
    (fun v w w' => by simp [realIP, mulVec_add, dotProduct_add])
    (fun c v w => by simp [realIP, mulVec_smul, dotProduct_smul])

theorem realIPForm_apply {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (v w : Fin g → ℂ) :
    realIPForm Y v w = realIP Y v w := rfl

theorem gram_det_eq_of_span_eq {g q k : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ)
    (v : Fin k → Fin g → ℂ) (hv : LinearIndependent ℤ v) (b : Fin q → Fin g → ℂ)
    (hb : LinearIndependent ℤ b)
    (hspan : Submodule.span ℤ (Set.range b) = Submodule.span ℤ (Set.range v)) :
    (Matrix.of fun i j => realIP Y (b i) (b j)).det =
      (Matrix.of fun i j => realIP Y (v i) (v j)).det := by
  obtain rfl : q = k := by
    have h1 := finrank_span_eq_card hb
    rw [hspan, finrank_span_eq_card hv] at h1
    simpa using h1.symm
  have hc : ∀ i, ∃ c : Fin q → ℤ, ∑ j, c j • v j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hd : ∀ j, ∃ d : Fin q → ℤ, ∑ i, d i • b i = v j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan.symm ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using hc
  choose d hd using hd
  have hdc : Matrix.of d * Matrix.of c = 1 := by
    ext j l
    refine Fintype.linearIndependent_iffₛ.mp hv (fun l => (Matrix.of d * Matrix.of c) j l)
      (fun l => (1 : Matrix (Fin q) (Fin q) ℤ) j l) ?_ l
    calc ∑ l, (Matrix.of d * Matrix.of c) j l • v l = ∑ i, d j i • b i := by
          simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, mul_smul]
          rw [Finset.sum_comm]
          simp only [← Finset.smul_sum, hc]
      _ = ∑ l, (1 : Matrix (Fin q) (Fin q) ℤ) j l • v l := by
          rw [hd j]
          simp [Matrix.one_apply]
  have hunit : IsUnit (Matrix.of c).det := by
    have := congrArg Matrix.det hdc
    rw [Matrix.det_mul, Matrix.det_one, mul_comm] at this
    exact IsUnit.of_mul_eq_one _ this
  have hsq : (((Matrix.of c).det : ℤ) : ℝ) ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h <;> simp [h]
  have hdet : ((Matrix.of c).map (Int.cast : ℤ → ℝ)).det = (((Matrix.of c).det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  have hG : (Matrix.of fun i j => realIP Y (b i) (b j)) =
      (Matrix.of c).map (Int.cast : ℤ → ℝ) * (Matrix.of fun i j => realIP Y (v i) (v j)) *
        ((Matrix.of c).map (Int.cast : ℤ → ℝ))ᵀ := by
    ext i l
    rw [Matrix.of_apply, ← hc i, ← hc l]
    show realIPForm Y (∑ j, c i j • v j) (∑ j, c l j • v j) = _
    simp only [map_sum, LinearMap.sum_apply]
    simp only [map_zsmul, LinearMap.smul_apply]
    simp only [zsmul_eq_mul, realIPForm_apply, Matrix.mul_apply, Matrix.map_apply,
      Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet]
  linear_combination (Matrix.of fun i j => realIP Y (v i) (v j)).det * hsq

theorem covolume_eq_gramCovol {g k : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (v : Fin k → Fin g → ℂ)
    (hv : LinearIndependent ℤ v) :
    GroundTheory.Heights₂.Heights.covolume Y v = gramCovol Y (Submodule.span ℤ (Set.range v)) := by
  unfold gramCovol
  have hS : {x : ℝ | ∃ (q : ℕ) (b : Fin q → Fin g → ℂ), LinearIndependent ℤ b ∧
      Submodule.span ℤ (Set.range b) = Submodule.span ℤ (Set.range v) ∧
      x = Real.sqrt (Matrix.of (fun i j => realIP Y (b i) (b j))).det} =
      {GroundTheory.Heights₂.Heights.covolume Y v} := by
    ext x
    constructor
    · rintro ⟨q, b, hb, hs, rfl⟩
      rw [Set.mem_singleton_iff, gram_det_eq_of_span_eq Y v hv b hb hs]
      rfl
    · rintro rfl
      exact ⟨k, v, hv, rfl, rfl⟩
  rw [hS, csInf_singleton]

theorem linearIndependent_leading {g r : ℕ} (hr : r ≤ g) :
    LinearIndependent ℤ (fun j : Fin r => (Pi.single (Fin.castLE hr j) (1 : ℂ) : Fin g → ℂ)) := by
  have h := (Pi.basisFun ℂ (Fin g)).linearIndependent.comp _ (Fin.castLE_injective hr)
  have h' : LinearIndependent ℂ
      (fun j : Fin r => (Pi.single (Fin.castLE hr j) (1 : ℂ) : Fin g → ℂ)) := by
    convert h using 1
    ext j
    simp
  exact h'.restrict_scalars' ℤ

theorem covolume_leading_eq_gramCovol_firstBlock {g r : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ)
    (hr : r ≤ g) :
    GroundTheory.Heights₂.Heights.covolume Y (fun j : Fin r => Pi.single (Fin.castLE hr j) (1 : ℂ)) =
      gramCovol Y (firstBlock hr) :=
  covolume_eq_gramCovol Y _ (linearIndependent_leading hr)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
