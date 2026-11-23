import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeGaussianBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValueHolomorphicEllipsoidStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeHermitianEllipsoidStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeFundamentalDomainHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicIntegralLeFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicContinuousIntegrableDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianNormTriangleInequalityStatement
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.ThetaJetMean

theorem L_cauchy (f : ℂ → ℂ) (a S : ℝ) (n i : ℕ) (hf : Differentiable ℂ f) (ha : 0 ≤ a) (hn : 1 ≤ n)
    (hb : ∀ t : ℂ, ‖f t‖ ^ 2 ≤ S ^ 2 * Real.exp (n * a * ‖t‖ ^ 2)) :
    ‖iteratedDeriv i f 0‖ ^ 2 ≤ (√(Real.exp 1 * n * i) ^ i * √a ^ i) ^ 2 * S ^ 2 :=
  GlobalTheory.T.iterated_derivative_gaussian_bound f a S n i hf ha hn hb

theorem L_subMean (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (φ : (Fin g → ℂ) → ℂ) (r : ℝ) (hH : Hm.PosDef)
    (hφ : Differentiable ℂ φ) (hr : 0 < r) :
    ENNReal.ofReal (‖φ 0‖ ^ 2) * volume {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} ≤
      ∫⁻ w in {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2}, ENNReal.ofReal (‖φ w‖ ^ 2) :=
  GlobalTheory.T.mean_value_holomorphic_ellipsoid g Hm φ r hH hφ hr

theorem L_ellVol (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (hH : Hm.PosDef) (hr : 0 < r) :
    volume {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} =
      ENNReal.ofReal (Real.pi ^ g * r ^ (2 * g) / (g.factorial * Hm.det.re)) :=
  GlobalTheory.T.volume_hermitian_ellipsoid' g Hm r hH hr

theorem L_covol (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ)) (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hH : Hm.PosDef) (hE : ∀ a b : Λ, (Ef a b : ℝ) = ((a : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (b : Fin g → ℂ))).im)
    (hEb : Function.Bijective Ef) (hFd : IsAddFundamentalDomain Λ Fd volume) :
    volume Fd = ENNReal.ofReal (1 / Hm.det.re) :=
  GlobalTheory.T.volume_fundamental_domain_hermitian g Λ Hm Ef Fd hs hH hE hEb hFd

theorem L_fold (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (F : (Fin g → ℂ) → ℝ)
    (Fd U : Set (Fin g → ℂ)) (hF : Continuous F) (hp : ∀ (l : Λ) z, F (z + l) = F z)
    (hFd : IsAddFundamentalDomain Λ Fd volume) (hU : MeasurableSet U)
    (hinj : ∀ u ∈ U, ∀ v ∈ U, u - v ∈ Λ → u = v) :
    ∫⁻ w in U, ENNReal.ofReal (F w) ≤ ∫⁻ z in Fd, ENNReal.ofReal (F z) :=
  GlobalTheory.T.periodic_integral_le_fundamental_domain g Λ F Fd U hF hp hFd hU hinj

theorem L_integ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (F : (Fin g → ℂ) → ℝ)
    (Fd : Set (Fin g → ℂ)) (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (hF : Continuous F)
    (hp : ∀ (l : Λ) z, F (z + l) = F z) (hFd : IsAddFundamentalDomain Λ Fd volume) :
    IntegrableOn F Fd volume :=
  GlobalTheory.T.periodic_continuous_integrable_domain g Λ F Fd hs hF hp hFd

theorem L_tri (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (hH : Hm.PosDef) :
    √(((a + b) ⬝ᵥ Hm.mulVec (star (a + b))).re) ≤ √((a ⬝ᵥ Hm.mulVec (star a)).re) + √((b ⬝ᵥ Hm.mulVec (star b)).re) :=
  GlobalTheory.T.hermitian_norm_triangle_inequality g Hm a b hH

theorem re_herm_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.PosDef) {z : Fin g → ℂ} (hz : z ≠ 0) :
    0 < (hermForm Hm z z).re := by
  have := hH.dotProduct_mulVec_pos (x := star z) (by simpa using hz)
  simp only [star_star] at this
  exact (Complex.pos_iff.1 this).1

theorem herm_conj {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.PosDef) (z w : Fin g → ℂ) :
    star (hermForm Hm w z) = hermForm Hm z w := by
  have h1 := hH.1
  simp only [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, star_sum, star_mul', star_star, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← h1.apply j i]; simp; ring

theorem re_herm_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (y : Fin g → ℂ) :
    (hermForm Hm (t • y) (t • y)).re = ‖t‖ ^ 2 * (hermForm Hm y y).re := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, Complex.star_def, mul_comm ((starRingEnd ℂ) t), Complex.mul_conj, Complex.re_ofReal_mul,
    Complex.normSq_eq_norm_sq]

theorem herm_add_re {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.PosDef) (z w : Fin g → ℂ) :
    (hermForm Hm (z + w) (z + w)).re =
      (hermForm Hm z z).re + 2 * (hermForm Hm w z).re + (hermForm Hm w w).re := by
  have h := herm_conj hH z w
  have e : hermForm Hm (z + w) (z + w) =
      hermForm Hm z z + hermForm Hm z w + hermForm Hm w z + hermForm Hm w w := by
    simp only [hermForm, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]; ring
  rw [e, ← h, Complex.star_def]
  simp only [Complex.add_re, Complex.conj_re]; ring

theorem herm_neg {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    hermForm Hm (-z) (-z) = hermForm Hm z z := by
  simp [hermForm, Matrix.mulVec_neg, dotProduct_neg]

theorem herm_zero_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    hermForm Hm 0 z = 0 := by simp [hermForm]

theorem ptwise (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Ef : LinearMap.BilinForm ℤ Λ) (ρ : ℝ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) (hn : 1 ≤ n)
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (hH : Hm.PosDef)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hEb : Function.Bijective Ef)
    (hρ : IsLeast {t | ∃ z ∈ Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} ρ) (hθ : Differentiable ℂ θ)
    (hper : ∀ (l : Λ) z, ‖θ (z + l)‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm (z + l) (z + l)).re)) =
      ‖θ z‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm z z).re)))
    (hFd : IsAddFundamentalDomain Λ Fd volume) (z0 : Fin g → ℂ) :
    ‖θ z0‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm z0 z0).re)) ≤
      (√(Real.exp 1 * g.factorial) * max ((√Real.pi / 2 * ρ)⁻¹ ^ g) (√n ^ g)) ^ 2 *
      ((∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm z z).re))) / (volume Fd).toReal) := by
  set F : (Fin g → ℂ) → ℝ := fun z => ‖θ z‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm z z).re)) with hFdef
  have hdet : 0 < Hm.det.re := (Complex.pos_iff.1 hH.det_pos).1
  have hHc : Continuous (fun z => hermForm Hm z z) := by unfold hermForm dotProduct Matrix.mulVec; fun_prop
  have hFc : Continuous F := by
    have := hθ.continuous
    fun_prop
  have hp : ∀ (l : Λ) z, F (z + l) = F z := hper
  have hint : IntegrableOn F Fd volume := L_integ g Λ F Fd hs hFc hp hFd
  have hvol : volume Fd = ENNReal.ofReal (1 / Hm.det.re) := L_covol g Λ Hm Ef Fd hs hH hE hEb hFd
  have hvolR : (volume Fd).toReal = 1 / Hm.det.re := by rw [hvol, ENNReal.toReal_ofReal (by positivity)]
  have hF0 : ∀ z, 0 ≤ F z := fun z => by positivity
  have hI0 : 0 ≤ ∫ z in Fd, F z := integral_nonneg hF0
  obtain ⟨⟨z1, -, hz1, hρeq⟩, hρle⟩ := hρ
  have hρpos : 0 < ρ := hρeq ▸ Real.sqrt_pos.2 (re_herm_pos hH hz1)
  set a : ℝ := (√Real.pi / 2 * ρ)⁻¹ with ha
  set b : ℝ := √(n : ℝ) with hb
  set m : ℝ := max a b with hm
  set M : ℝ := max (a ^ g) (b ^ g) with hM
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hapos : 0 < a := by positivity
  have hbpos : 0 < b := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hmpos : 0 < m := lt_max_of_lt_left hapos
  set r : ℝ := 1 / (√Real.pi * m) with hr
  have hrpos : 0 < r := by positivity
  have hpr2 : Real.pi * r ^ 2 = 1 / m ^ 2 := by
    rw [hr, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]; field_simp
  have hnr : Real.pi * n * r ^ 2 ≤ 1 := by
    have hb2 : (n : ℝ) = b ^ 2 := by rw [hb, Real.sq_sqrt (by positivity)]
    have hbm : b ≤ m := le_max_right _ _
    have e : Real.pi * n * r ^ 2 = n / m ^ 2 := by rw [mul_right_comm, hpr2]; field_simp
    rw [e, div_le_one (by positivity), hb2]
    exact pow_le_pow_left₀ hbpos.le hbm 2
  have h2r : 2 * r ≤ ρ := by
    have ham : a ≤ m := le_max_left _ _
    have : r ≤ 1 / (√Real.pi * a) := by
      rw [hr]; exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left ham hpi.le)
    have e : 1 / (√Real.pi * a) = ρ / 2 := by rw [ha]; field_simp
    linarith
  have hmM : m ^ g ≤ M := by
    rcases le_total a b with h | h
    · rw [hm, max_eq_right h]; exact le_max_right _ _
    · rw [hm, max_eq_left h]; exact le_max_left _ _
  have key : 1 ≤ (Real.pi * r ^ 2) ^ g * M ^ 2 := by
    rw [hpr2, div_pow, one_pow, ← pow_mul]
    rw [one_div_mul_eq_div, one_le_div (by positivity)]
    calc m ^ (2 * g) = (m ^ g) ^ 2 := by rw [← pow_mul, mul_comm]
      _ ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) hmM 2

  set φ : (Fin g → ℂ) → ℂ := fun w => θ (z0 + w) *
    Complex.exp (-(Real.pi * n * hermForm Hm w z0) - Real.pi * n / 2 * hermForm Hm z0 z0) with hφ
  have hlin : Differentiable ℂ (fun w : Fin g → ℂ => hermForm Hm w z0) := by
    unfold hermForm dotProduct
    fun_prop
  have hφd : Differentiable ℂ φ := by
    have h1 : Differentiable ℂ (fun w : Fin g → ℂ => θ (z0 + w)) := hθ.comp (differentiable_const _ |>.add differentiable_id)
    have h2 := hlin
    fun_prop
  have hφnorm : ∀ w, ‖φ w‖ ^ 2 = F (z0 + w) * Real.exp (Real.pi * n * (hermForm Hm w w).re) := by
    intro w
    simp only [hφ, hFdef, norm_mul, Complex.norm_exp, mul_pow]
    rw [herm_add_re hH z0 w, mul_assoc (‖θ (z0 + w)‖ ^ 2), ← Real.exp_add, ← Real.exp_nat_mul]
    congr 2
    simp [Complex.mul_re, Complex.div_ofNat_re]
    ring
  have hφ0 : ‖φ 0‖ ^ 2 = F z0 := by
    rw [hφnorm 0]; simp [herm_zero_left]
  set B : Set (Fin g → ℂ) := {w | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} with hB
  set U : Set (Fin g → ℂ) := {u | ((u - z0) ⬝ᵥ Hm.mulVec (star (u - z0))).re < r ^ 2} with hU
  have hBm : MeasurableSet B := (isOpen_lt (Complex.continuous_re.comp hHc) continuous_const).measurableSet
  have hUm : MeasurableSet U :=
    (isOpen_lt (Complex.continuous_re.comp (hHc.comp (continuous_id.sub continuous_const))) continuous_const).measurableSet
  have hinj : ∀ u ∈ U, ∀ v ∈ U, u - v ∈ Λ → u = v := by
    intro u hu v hv hl
    by_contra hne
    have hl0 : u - v ≠ 0 := sub_ne_zero.2 hne
    have h1 : ρ ≤ √(hermForm Hm (u - v) (u - v)).re := hρle ⟨u - v, hl, hl0, rfl⟩
    have h2 : √(hermForm Hm (u - v) (u - v)).re ≤
        √(hermForm Hm (u - z0) (u - z0)).re + √(hermForm Hm (z0 - v) (z0 - v)).re := by
      have := L_tri g Hm (u - z0) (z0 - v) hH
      rwa [sub_add_sub_cancel] at this
    have e : hermForm Hm (z0 - v) (z0 - v) = hermForm Hm (v - z0) (v - z0) := by rw [← neg_sub, herm_neg]
    have h3 : √(hermForm Hm (u - z0) (u - z0)).re < r := (Real.sqrt_lt' hrpos).2 hu
    have h4 : √(hermForm Hm (v - z0) (v - z0)).re < r := (Real.sqrt_lt' hrpos).2 hv
    rw [e] at h2
    have k : ρ < 2 * r := by
      calc ρ ≤ _ := h1
        _ ≤ _ := h2
        _ < r + r := add_lt_add h3 h4
        _ = 2 * r := by ring
    exact absurd h2r (not_le.2 k)
  have c1 := L_subMean g Hm φ r hH hφd hrpos
  have c2 : ∫⁻ w in B, ENNReal.ofReal (‖φ w‖ ^ 2) ≤ ∫⁻ w in B, ENNReal.ofReal (Real.exp 1 * F (z0 + w)) := by
    refine setLIntegral_mono' hBm fun w hw => ENNReal.ofReal_le_ofReal ?_
    rw [hφnorm, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (hF0 _)
    refine Real.exp_le_exp.2 ?_
    have : (hermForm Hm w w).re < r ^ 2 := hw
    have h5 := mul_le_mul_of_nonneg_left this.le (by positivity : (0 : ℝ) ≤ Real.pi * n)
    linarith
  have c3 : ∫⁻ w in B, ENNReal.ofReal (Real.exp 1 * F (z0 + w)) =
      ENNReal.ofReal (Real.exp 1) * ∫⁻ w in B, ENNReal.ofReal (F (z0 + w)) := by
    simp_rw [ENNReal.ofReal_mul (Real.exp_pos 1).le]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have c4 : ∫⁻ w in B, ENNReal.ofReal (F (z0 + w)) = ∫⁻ u in U, ENNReal.ofReal (F u) := by
    have hpre : (fun w => z0 + w) ⁻¹' U = B := by
      ext w; simp [hU, hB]
    rw [← hpre]
    exact (measurePreserving_add_left volume z0).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addLeft z0) (fun u => ENNReal.ofReal (F u)) U
  have c5 := L_fold g Λ F Fd U hFc hp hFd hUm hinj
  have c6 : ∫⁻ z in Fd, ENNReal.ofReal (F z) = ENNReal.ofReal (∫ z in Fd, F z) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hF0)).symm
  have hVB := L_ellVol g Hm r hH hrpos
  have hall : ENNReal.ofReal (F z0) * ENNReal.ofReal (Real.pi ^ g * r ^ (2 * g) / (g.factorial * Hm.det.re)) ≤
      ENNReal.ofReal (Real.exp 1 * ∫ z in Fd, F z) := by
    rw [← hVB, ← hφ0, ENNReal.ofReal_mul (Real.exp_pos 1).le, ← c6]
    calc _ ≤ _ := c1
      _ ≤ _ := c2
      _ = _ := c3
      _ = _ := by rw [c4]
      _ ≤ _ := by gcongr
  rw [← ENNReal.ofReal_mul (hF0 z0), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hall
  have hpow : Real.pi ^ g * r ^ (2 * g) = (Real.pi * r ^ 2) ^ g := by rw [mul_pow, pow_mul]
  rw [hvolR]
  change F z0 ≤ _
  have hg : (0 : ℝ) < g.factorial := by exact_mod_cast g.factorial_pos
  calc F z0 ≤ F z0 * ((Real.pi * r ^ 2) ^ g * M ^ 2) := le_mul_of_one_le_right (hF0 z0) key
    _ = (F z0 * (Real.pi ^ g * r ^ (2 * g) / (g.factorial * Hm.det.re))) * (g.factorial * Hm.det.re * M ^ 2) := by
      rw [hpow]; field_simp
    _ ≤ (Real.exp 1 * ∫ z in Fd, F z) * (g.factorial * Hm.det.re * M ^ 2) :=
      mul_le_mul_of_nonneg_right hall (by positivity)
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; field_simp

theorem theta_jet_le_l2_norm : ∀ (g n i : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (ρ : ℝ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) (y : Fin g → ℂ), 1 ≤ n → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.PosDef → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → IsLeast {t | ∃ z ∈ Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} ρ → Differentiable ℂ θ → (∀ (l : Λ) z, ‖θ (z + l)‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm (z + l) (z + l)).re)) = ‖θ z‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm z z).re))) → IsAddFundamentalDomain Λ Fd volume → ‖iteratedDeriv i (fun t : ℂ => θ (t • y)) 0‖ ^ 2 ≤ (jetBd g n i ρ * √(Real.pi * (hermForm Hm y y).re) ^ i) ^ 2 * ((∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm z z).re))) / (volume Fd).toReal) := by
  intro g n i Λ _ Hm Ef ρ θ Fd y hn hs hH hE hEb hρ hθ hper hFd
  have hpt := ptwise g n Λ Hm Ef ρ θ Fd hn hs hH hE hEb hρ hθ hper hFd
  set A := (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm z z).re))) / (volume Fd).toReal with hA
  set C0 := (√(Real.exp 1 * g.factorial) * max ((√Real.pi / 2 * ρ)⁻¹ ^ g) (√n ^ g)) ^ 2 with hC0
  have hA0 : 0 ≤ A := div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg
  have hCA : 0 ≤ C0 * A := mul_nonneg (sq_nonneg _) hA0
  have hy0 : 0 ≤ (hermForm Hm y y).re := by
    rcases eq_or_ne y 0 with rfl | hy
    · simp [hermForm]
    · exact (re_herm_pos hH hy).le
  have hc := L_cauchy (fun t : ℂ => θ (t • y)) (Real.pi * (hermForm Hm y y).re) (√(C0 * A)) n i
    (hθ.comp (differentiable_id.smul_const y)) (by positivity) hn (by
      intro t
      have h := hpt (t • y)
      rw [re_herm_smul] at h
      rw [Real.sq_sqrt hCA]
      have hX : ‖θ (t • y)‖ ^ 2 = (‖θ (t • y)‖ ^ 2 *
          Real.exp (-(Real.pi * n * (‖t‖ ^ 2 * (hermForm Hm y y).re)))) *
          Real.exp (Real.pi * n * (‖t‖ ^ 2 * (hermForm Hm y y).re)) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      rw [hX, show (n : ℝ) * (Real.pi * (hermForm Hm y y).re) * ‖t‖ ^ 2 =
        Real.pi * n * (‖t‖ ^ 2 * (hermForm Hm y y).re) by ring]
      exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le)
  rw [Real.sq_sqrt hCA] at hc
  refine hc.trans (le_of_eq ?_)
  rw [hC0, jetBd]
  ring

end GlobalTheory.ThetaJetMean
end
