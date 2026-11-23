import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.SecLineB

noncomputable section

open MeasureTheory MvPolynomial Filter Topology

namespace PositivityTheory.Rg.Sw.FFTSteps

namespace SecondLineEstimates

variable {m n : ℕ}

def hk (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (x : Fin m → Fin n → ℂ) : ℂ :=
  evX P x * gs c x * (Complex.I * t * (b * gramX ε x).trace) ^ k

def Fk (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ → ℂ :=
  fun z => ∫ x : Fin m → Fin n → ℂ, hk ε c t P b k x * Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)

def dl (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : ℝ := c / (4 * (|t| * kb b + 1))

lemma dl_pos {c : ℝ} (hc : 0 < c) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : 0 < dl c t b := by
  have := kb_nonneg b
  unfold dl; positivity

lemma dl_mul {c : ℝ} (hc : 0 < c) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : |t| * dl c t b * kb b ≤ c / 4 := by
  have hk := kb_nonneg b
  have hA : 0 ≤ |t| * kb b := by positivity
  have h1 : |t| * dl c t b * kb b = c / 4 * (|t| * kb b / (|t| * kb b + 1)) := by
    unfold dl; field_simp
  rw [h1]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))

lemma norm_gs (c : ℝ) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ = Real.exp (-c * sq x) := by
  unfold gs sq
  rw [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, neg_mul]

lemma norm_cexp_le (t : ℝ) (z T : ℂ) (hT : T.im = 0) :
    ‖Complex.exp (Complex.I * t * z * T)‖ ≤ Real.exp (|t| * |z.im| * ‖T‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * t * z * T).re = -(t * z.im * T.re) := by
    simp [Complex.mul_re, Complex.mul_im, hT]
  rw [hre]
  calc -(t * z.im * T.re) ≤ |t * z.im * T.re| := neg_le_abs _
    _ = |t| * |z.im| * |T.re| := by rw [abs_mul, abs_mul]
    _ ≤ |t| * |z.im| * ‖T‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm T) (by positivity)

variable (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ)

lemma cexp_bound (hb : b.IsHermitian) (hc : 0 < c) (z : ℂ) (hz : |z.im| ≤ dl c t b) (x : Fin m → Fin n → ℂ) :
    ‖Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)‖ ≤ Real.exp (c / 4 * sq x) := by
  refine (norm_cexp_le t z _ (trace_im ε b hb x)).trans (Real.exp_le_exp.mpr ?_)
  have h1 := norm_trace_le ε b x
  have hs := sq_nonneg' x
  have hk := kb_nonneg b
  have hd := (dl_pos hc t b).le
  calc |t| * |z.im| * ‖(b * gramX ε x).trace‖ ≤ |t| * dl c t b * (kb b * sq x) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hz (abs_nonneg _)) h1 (norm_nonneg _) (by positivity)
    _ = (|t| * dl c t b * kb b) * sq x := by ring
    _ ≤ c / 4 * sq x := mul_le_mul_of_nonneg_right (dl_mul hc t b) hs

lemma hk_bound (Cp : ℝ) (hCp : 0 ≤ Cp) (D : ℕ) (hP : ∀ x, ‖evX P x‖ ≤ Cp * (1 + sq x) ^ D) (k : ℕ)
    (x : Fin m → Fin n → ℂ) :
    ‖hk ε c t P b k x‖ ≤ Cp * (|t| * kb b) ^ k * ((1 + sq x) ^ (D + k) * Real.exp (-c * sq x)) := by
  have hs := sq_nonneg' x
  have hkb := kb_nonneg b
  have hT : ‖Complex.I * t * (b * gramX ε x).trace‖ ≤ |t| * kb b * (1 + sq x) := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    calc |t| * ‖(b * gramX ε x).trace‖ ≤ |t| * (kb b * sq x) :=
          mul_le_mul_of_nonneg_left (norm_trace_le ε b x) (abs_nonneg _)
      _ ≤ |t| * (kb b * (1 + sq x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hkb) (abs_nonneg _)
      _ = |t| * kb b * (1 + sq x) := by ring
  unfold hk
  rw [norm_mul, norm_mul, norm_pow, norm_gs]
  calc ‖evX P x‖ * Real.exp (-c * sq x) * ‖Complex.I * t * (b * gramX ε x).trace‖ ^ k
      ≤ Cp * (1 + sq x) ^ D * Real.exp (-c * sq x) * (|t| * kb b * (1 + sq x)) ^ k :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hP x) (Real.exp_pos _).le)
          (pow_le_pow_left₀ (norm_nonneg _) hT k) (by positivity) (by positivity)
    _ = Cp * (|t| * kb b) ^ k * ((1 + sq x) ^ (D + k) * Real.exp (-c * sq x)) := by
        rw [mul_pow (|t| * kb b), pow_add]; ring

lemma int_bound (hb : b.IsHermitian) (hc : 0 < c) (Cp : ℝ) (hCp : 0 ≤ Cp) (D : ℕ)
    (hP : ∀ x, ‖evX P x‖ ≤ Cp * (1 + sq x) ^ D) (k : ℕ) (z : ℂ) (hz : |z.im| ≤ dl c t b)
    (x : Fin m → Fin n → ℂ) :
    ‖hk ε c t P b k x * Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)‖ ≤
      Cp * (|t| * kb b) ^ k * ((1 + sq x) ^ (D + k) * Real.exp (-(3 * c / 4) * sq x)) := by
  have hs := sq_nonneg' x
  have hkb := kb_nonneg b
  rw [norm_mul]
  calc ‖hk ε c t P b k x‖ * ‖Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)‖
      ≤ Cp * (|t| * kb b) ^ k * ((1 + sq x) ^ (D + k) * Real.exp (-c * sq x)) * Real.exp (c / 4 * sq x) :=
        mul_le_mul (hk_bound ε c t P b Cp hCp D hP k x) (cexp_bound ε c t b hb hc z hz x) (norm_nonneg _)
          (by positivity)
    _ = Cp * (|t| * kb b) ^ k * ((1 + sq x) ^ (D + k) * Real.exp (-(3 * c / 4) * sq x)) := by
        rw [mul_assoc, mul_assoc ((1 + sq x) ^ (D + k)), ← Real.exp_add]; ring_nf

lemma continuous_integrand (k : ℕ) (z : ℂ) :
    Continuous (fun x : Fin m → Fin n → ℂ => hk ε c t P b k x * Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)) := by
  unfold hk gs
  have h1 := continuous_evX P
  have h2 := continuous_trace ε b
  have h3 : Continuous (fun x : Fin m → Fin n → ℂ => ∑ a, ∑ i, ‖x a i‖ ^ 2) := continuous_sq
  fun_prop

lemma hasDerivAt_Fk (hb : b.IsHermitian) (hc : 0 < c) (Cp : ℝ) (hCp : 0 ≤ Cp) (D : ℕ)
    (hP : ∀ x, ‖evX P x‖ ≤ Cp * (1 + sq x) ^ D) (k : ℕ) (z₀ : ℂ) (hz₀ : |z₀.im| < dl c t b) :
    HasDerivAt (Fk ε c t P b k) (Fk ε c t P b (k + 1) z₀) z₀ := by
  have hSo : IsOpen {z : ℂ | |z.im| < dl c t b} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hS : {z : ℂ | |z.im| < dl c t b} ∈ 𝓝 z₀ := hSo.mem_nhds hz₀
  have hbd : ∀ j, Integrable (fun x : Fin m → Fin n → ℂ =>
      Cp * (|t| * kb b) ^ j * ((1 + sq x) ^ (D + j) * Real.exp (-(3 * c / 4) * sq x))) := fun j =>
    (integrable_poly_gauss (D + j) (by positivity)).const_mul _
  have hint : Integrable (fun x : Fin m → Fin n → ℂ =>
      hk ε c t P b k x * Complex.exp (Complex.I * t * z₀ * (b * gramX ε x).trace)) :=
    (hbd k).mono' (continuous_integrand ε c t P b k z₀).aestronglyMeasurable
      (Eventually.of_forall fun x => int_bound ε c t P b hb hc Cp hCp D hP k z₀ hz₀.le x)
  have hder : ∀ (x : Fin m → Fin n → ℂ) (z : ℂ), HasDerivAt
      (fun z => hk ε c t P b k x * Complex.exp (Complex.I * t * z * (b * gramX ε x).trace))
      (hk ε c t P b (k + 1) x * Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)) z := by
    intro x z
    have h1 : HasDerivAt (fun z : ℂ => Complex.I * t * z * (b * gramX ε x).trace)
        (Complex.I * t * (b * gramX ε x).trace) z := by
      simpa using ((hasDerivAt_id z).const_mul (Complex.I * t)).mul_const ((b * gramX ε x).trace)
    have h2 := (h1.cexp).const_mul (hk ε c t P b k x)
    refine h2.congr_deriv ?_
    simp only [hk, pow_succ]; ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z x => hk ε c t P b k x * Complex.exp (Complex.I * t * z * (b * gramX ε x).trace))
    (F' := fun z x => hk ε c t P b (k + 1) x * Complex.exp (Complex.I * t * z * (b * gramX ε x).trace))
    (bound := fun x => Cp * (|t| * kb b) ^ (k + 1) * ((1 + sq x) ^ (D + (k + 1)) * Real.exp (-(3 * c / 4) * sq x)))
    hS (Eventually.of_forall fun z => (continuous_integrand ε c t P b k z).aestronglyMeasurable) hint
    ((continuous_integrand ε c t P b (k + 1) z₀).aestronglyMeasurable)
    (ae_of_all _ fun x z hz => int_bound ε c t P b hb hc Cp hCp D hP (k + 1) z (le_of_lt hz) x)
    (hbd (k + 1)) (ae_of_all _ fun x z _ => hder x z)
  exact key.2

lemma iter (hb : b.IsHermitian) (hc : 0 < c) (Cp : ℝ) (hCp : 0 ≤ Cp) (D : ℕ)
    (hP : ∀ x, ‖evX P x‖ ≤ Cp * (1 + sq x) ^ D) (k : ℕ) :
    ∀ z : ℂ, |z.im| < dl c t b → iteratedDeriv k (Fk ε c t P b 0) z = Fk ε c t P b k z := by
  have hSo : IsOpen {z : ℂ | |z.im| < dl c t b} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (Fk ε c t P b 0) =ᶠ[𝓝 z] Fk ε c t P b k :=
      Filter.eventuallyEq_of_mem (hSo.mem_nhds hz) fun w hw => ih w hw
    rw [heq.deriv_eq]
    exact (hasDerivAt_Fk ε c t P b hb hc Cp hCp D hP k z hz).deriv

end SecondLineEstimates

open SecondLineEstimates in
theorem secLine : SecLine := by
  intro m n ε c t hc P b hb
  obtain ⟨Cp, hCp, D, hP⟩ := evX_bound P
  have hF : (fun z : ℂ => ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x *
      Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)) = Fk ε c t P b 0 := by
    funext z; simp [Fk, hk]
  refine ⟨dl c t b, dl_pos hc t b, ?_, ?_, ?_⟩
  · rw [hF]
    intro z hz
    exact (hasDerivAt_Fk ε c t P b hb hc Cp hCp D hP 0 z hz).differentiableAt.differentiableWithinAt
  · intro z _
    simp only [secN, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_assoc]
  · intro k
    rw [hF, iter ε c t P b hb hc Cp hCp D hP k 0 (by simpa using dl_pos hc t b)]
    simp only [Fk, hk, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [← integral_const_mul]
    congr 1; funext x; rw [mul_pow]; ring

end PositivityTheory.Rg.Sw.FFTSteps
