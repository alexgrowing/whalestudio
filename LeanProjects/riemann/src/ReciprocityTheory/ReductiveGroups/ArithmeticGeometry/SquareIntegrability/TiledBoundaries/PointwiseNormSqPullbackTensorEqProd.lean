import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaNA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement

namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries

open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex

noncomputable section

def StepT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (n : ℕ) (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (g : (Fin n → Vsp X.dim) → F), Continuous g →
    (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v, g (v + γ) = g v) →
    ∀ a, (⨍ v in X.fd n, g (v - a)) = ⨍ v in X.fd n, g v

def StepI : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (n : ℕ) (g : (Fin n → Vsp X.dim) → ℂ),
    Continuous g → IntegrableOn g (X.fd n)

def StepF : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (n : ℕ) (f : Vsp X.dim → ℝ), Continuous f →
    (⨍ v in X.fd n, ∏ k, f (v k)) = (⨍ w in ZSpan.fundamentalDomain X.b, f w) ^ n

def StepP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (q : ℕ) (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim),
    1 ≤ q → IsPi X q π → ∀ g : Vsp X.dim → ℝ, Continuous g →
    (∀ γ ∈ X.L, ∀ v, g (v + γ) = g v) →
    (⨍ w in ZSpan.fundamentalDomain X.b, g (π w)) = ⨍ w in ZSpan.fundamentalDomain X.b, g w

def StepPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (q n : ℕ) (F : (Fin n → Vsp X.dim) → ℂ),
    F ∈ X.Sec q n → F ≠ 0 → 0 < X.l2 q F

def StepDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (x : Vsp X.dim),
    (∀ y ∈ X.L, ∃ m : ℤ, (Hf x y).im = m) → x ∈ X.L

def StepK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (q n : ℕ) (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim),
    1 ≤ q → IsPi X q π → ∀ K, IsReps X q n π K → q ^ (Fintype.card (Idx X.dim) * n) ≤ K.card

def StepD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (q n : ℕ), 1 ≤ q →
    FiniteDimensional ℂ (X.Sec q n) ∧
      Module.finrank ℂ (X.Sec q n) ≤ q ^ (Fintype.card (Idx X.dim) * n)

section Elem

variable {E : Type} [Field E] [NumberField E]

theorem cont_HC {ι : Type} [Fintype ι] {n : ℕ} :
    Continuous (fun v : Fin n → EuclideanSpace ℂ ι => HC v v) := by
  unfold HC Hf
  fun_prop

theorem continuous_pointNormSq_quotient (X : PT E) (q : ℕ) {n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : Continuous F) :
    Continuous (X.ptN2 q F) := by
  unfold PT.ptN2
  exact (hF.norm.pow 2).mul (Real.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_re.comp cont_HC)))

theorem cont_ip (q : ℕ) {n : ℕ} {ι : Type} [Fintype ι] {F G : (Fin n → EuclideanSpace ℂ ι) → ℂ}
    (hF : Continuous F) (hG : Continuous G) :
    Continuous (fun v => F v * (starRingEnd ℂ) (G v) *
      ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) := by
  exact (hF.mul (Complex.continuous_conj.comp hG)).mul (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp cont_HC))))

theorem pointwiseNormSq_pullback_tensor_eq_prod (X : PT E) {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hπ : IsPi X q π)
    (s : (Fin 1 → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim) :
    X.ptN2 q (s0 X π s) v = ∏ k, X.ptN2 1 s (fun _ => π (v k)) := by
  unfold PT.ptN2 s0
  rw [Finset.prod_mul_distrib, norm_prod, ← Finset.prod_pow, ← Real.exp_sum]
  congr 2
  simp only [HC, Fin.sum_univ_one, hπ.2.2.1, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.mul_re]
  ring

theorem pi_bij (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q)
    (hπ : IsPi X q π) : Function.Bijective π := by
  have hinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have h0 : (q : ℂ) * Hf v v = 0 := by
      rw [← hπ.2.2.1 v v, hv]
      simp [Hf]
    have h1 : Hf v v = 0 := (mul_eq_zero.1 h0).resolve_left hq
    have h2 : ∑ i, Complex.normSq (v i) = 0 := by
      have := congrArg Complex.re h1
      simpa [Hf, Complex.mul_conj, Complex.re_sum] using this
    ext i
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))).1 h2 i
      (Finset.mem_univ _)
    simpa using h3
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

theorem l2Inner_smul (X : PT E) (q : ℕ) {n : ℕ} (c c' : ℂ) (F G : (Fin n → Vsp X.dim) → ℂ) :
    X.l2ip q (fun v => c * F v) (fun v => c' * G v) = c * (starRingEnd ℂ) c' * X.l2ip q F G := by
  unfold PT.l2ip
  simp only [MeasureTheory.setAverage_eq]
  rw [mul_smul_comm, ← MeasureTheory.integral_const_mul]
  congr 2
  funext v
  simp only [map_mul]
  ring

theorem l2Inner_self (X : PT E) (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ) :
    X.l2ip q F F = (X.l2 q F : ℂ) := by
  unfold PT.l2ip PT.l2 PT.ptN2
  simp only [MeasureTheory.setAverage_eq]
  rw [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem l2Inner_zero_left (X : PT E) (q : ℕ) {n : ℕ} (G : (Fin n → Vsp X.dim) → ℂ) :
    X.l2ip q 0 G = 0 := by
  unfold PT.l2ip
  simp

theorem l2Inner_sum_left (hI : StepI) (X : PT E) (q : ℕ) {n : ℕ} {ι : Type} (t : Finset ι) (g : ι → ℂ)
    (F : ι → (Fin n → Vsp X.dim) → ℂ) (G : (Fin n → Vsp X.dim) → ℂ) (hF : ∀ j, Continuous (F j))
    (hG : Continuous G) :
    X.l2ip q (fun v => ∑ j ∈ t, g j * F j v) G = ∑ j ∈ t, g j * X.l2ip q (F j) G := by
  unfold PT.l2ip
  simp only [MeasureTheory.setAverage_eq]
  have hi : ∀ j, IntegrableOn (fun v => F j v * (starRingEnd ℂ) (G v) *
      ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) (X.fd n) :=
    fun j => hI E X n _ (cont_ip q (hF j) hG)
  have hsum : (fun v => (∑ j ∈ t, g j * F j v) * (starRingEnd ℂ) (G v) *
      ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) = fun v => ∑ j ∈ t, g j *
      (F j v * (starRingEnd ℂ) (G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) := by
    funext v
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, MeasureTheory.integral_finset_sum _ (fun j _ => (hi j).const_mul (g j)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul, mul_smul_comm]

end Elem

end

end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
