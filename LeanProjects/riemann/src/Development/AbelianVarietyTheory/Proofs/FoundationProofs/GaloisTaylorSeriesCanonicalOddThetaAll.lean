import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsMulEqPolynomialWeierstrassP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Topology
open Filter

noncomputable section

namespace GlobalTheory.SigmaConj

section Formal

open PowerSeries

variable {R S : Type} [CommRing R] [CommRing S]

def wSer (s : R) (A : R⟦X⟧) : R⟦X⟧ :=
  d⁄dX R A ^ 2 - A * d⁄dX R (d⁄dX R A) - C s * A ^ 2

def OdeSer (s a b : R) (A : R⟦X⟧) : Prop :=
  (d⁄dX R (wSer s A) * A - 2 * wSer s A * d⁄dX R A) ^ 2 =
    4 * wSer s A ^ 3 - C a * wSer s A * A ^ 4 - C b * A ^ 6

def homSer (m : ℕ) (q : ℕ → R) (s : R) (A : R⟦X⟧) : R⟦X⟧ :=
  ∑ k ∈ Finset.range (m + 1), C (q k) * (wSer s A ^ k * A ^ (2 * (m - k)))

def EndSer (α : R) (N m : ℕ) (q : ℕ → R) (s : R) (A : R⟦X⟧) : Prop :=
  rescale α A ^ 2 * A ^ (2 * m) = A ^ (2 * N) * homSer m q s A

lemma map_deriv (φ : R →+* S) (A : R⟦X⟧) : map φ (d⁄dX R A) = d⁄dX S (map φ A) := by
  ext n; simp [coeff_derivative]

lemma map_rescale (φ : R →+* S) (α : R) (A : R⟦X⟧) :
    map φ (rescale α A) = rescale (φ α) (map φ A) := by
  ext n; simp [coeff_rescale]

lemma map_wSer (φ : R →+* S) (s : R) (A : R⟦X⟧) : map φ (wSer s A) = wSer (φ s) (map φ A) := by
  simp [wSer, map_deriv]

lemma OdeSer.map (φ : R →+* S) {s a b : R} {A : R⟦X⟧} (h : OdeSer s a b A) :
    OdeSer (φ s) (φ a) (φ b) (map φ A) := by
  have := congrArg (PowerSeries.map φ) h
  simpa [OdeSer, map_deriv, map_wSer, map_ofNat] using this

lemma OdeSer.of_map (φ : R →+* S) (hφ : Function.Injective φ) {s a b : R} {A : R⟦X⟧}
    (h : OdeSer (φ s) (φ a) (φ b) (PowerSeries.map φ A)) : OdeSer s a b A := by
  apply PowerSeries.map_injective φ hφ
  simpa [OdeSer, map_deriv, map_wSer, map_ofNat] using h

lemma EndSer.map (φ : R →+* S) {α s : R} {N m : ℕ} {q : ℕ → R} {A : R⟦X⟧}
    (h : EndSer α N m q s A) : EndSer (φ α) N m (fun k => φ (q k)) (φ s) (map φ A) := by
  have := congrArg (PowerSeries.map φ) h
  simpa [EndSer, homSer, map_rescale, map_wSer] using this

lemma EndSer.descend {M : Type} [Field M] [Algebra M ℂ] {α s : M} {N m : ℕ} {q : ℕ → ℂ}
    {A : M⟦X⟧} (h : EndSer (algebraMap M ℂ α) N m q (algebraMap M ℂ s)
      (PowerSeries.map (algebraMap M ℂ) A)) : ∃ q' : ℕ → M, EndSer α N m q' s A := by
  obtain ⟨r, hr⟩ := (Algebra.linearMap M ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap M ℂ).injective)
  have hr' : ∀ x : M, r (algebraMap M ℂ x) = x := fun x => LinearMap.congr_fun hr x
  refine ⟨fun k => r (q k), ?_⟩
  ext n
  have h1 := congrArg (fun B => r (coeff n B)) h
  have c1 : ∀ (x y : ℂ⟦X⟧) (c : ℂ), x * (C c * y) = C c * (x * y) := fun x y c => by ring
  have c2 : ∀ (x y : M⟦X⟧) (c : M), x * (C c * y) = C c * (x * y) := fun x y c => by ring
  simp only [homSer, Finset.mul_sum, c1, ← map_rescale, ← map_wSer,
    ← map_pow (PowerSeries.map (algebraMap M ℂ)), ← map_mul (PowerSeries.map (algebraMap M ℂ)),
    map_sum, coeff_C_mul, coeff_map, hr'] at h1
  simp only [homSer, Finset.mul_sum, c2, map_sum, coeff_C_mul]
  rw [h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm (q k), ← Algebra.smul_def, r.map_smul, smul_eq_mul, mul_comm (r (q k))]

lemma ode_unique {a b : ℂ} {P Q : ℂ⟦X⟧} (hP0 : constantCoeff P = 1) (hQ0 : constantCoeff Q = 1)
    (hP : (X * d⁄dX ℂ P - 2 * P) ^ 2 = 4 * P ^ 3 - C a * X ^ 4 * P - C b * X ^ 6)
    (hQ : (X * d⁄dX ℂ Q - 2 * Q) ^ 2 = 4 * Q ^ 3 - C a * X ^ 4 * Q - C b * X ^ 6) : P = Q := by
  by_contra hne
  have hD : P - Q ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨n, E, hE, hE0⟩ : ∃ (n : ℕ) (E : ℂ⟦X⟧), P = Q + X ^ n * E ∧ constantCoeff E ≠ 0 :=
    ⟨(P - Q).order.toNat, divXPowOrder (P - Q), by rw [X_pow_order_mul_divXPowOrder]; ring,
      by simpa [constantCoeff_divXPowOrder_eq_zero_iff] using hD⟩
  have hx : (X : ℂ⟦X⟧) * d⁄dX ℂ (X ^ n : ℂ⟦X⟧) = (n : ℂ⟦X⟧) * X ^ n := by
    cases n with
    | zero => simp
    | succ n => simp [Derivation.leibniz_pow]; ring
  have hd : X * d⁄dX ℂ P = X * d⁄dX ℂ Q + X ^ n * ((n : ℂ⟦X⟧) * E + X * d⁄dX ℂ E) := by
    rw [hE, map_add, Derivation.leibniz]
    simp only [smul_eq_mul]
    linear_combination E * hx
  have key : X ^ n * ((((n : ℂ⟦X⟧) * E + X * d⁄dX ℂ E) - 2 * E) *
      (X * d⁄dX ℂ P - 2 * P + (X * d⁄dX ℂ Q - 2 * Q))) =
      X ^ n * (E * (4 * (P ^ 2 + P * Q + Q ^ 2) - C a * X ^ 4)) := by
    have e : X ^ n * E = P - Q := by rw [hE]; ring
    linear_combination hP - hQ - (X * d⁄dX ℂ P - 2 * P + (X * d⁄dX ℂ Q - 2 * Q)) * hd
      - (2 * (X * d⁄dX ℂ P - 2 * P + (X * d⁄dX ℂ Q - 2 * Q))
        + (4 * (P ^ 2 + P * Q + Q ^ 2) - C a * X ^ 4)) * e
  have k2 := congrArg constantCoeff (mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ))) key)
  simp [hP0, hQ0, map_ofNat] at k2
  have : ((n : ℂ) + 1) * constantCoeff E = 0 := by linear_combination (-1 / 4 : ℂ) * k2
  exact (mul_ne_zero (Nat.cast_add_one_ne_zero n) hE0) this

lemma ode_reduce {s a b : ℂ} {U V : ℂ⟦X⟧} (hUV : U * V = 1) (h : OdeSer s a b (X * U)) :
    (X * d⁄dX ℂ (wSer s (X * U) * V ^ 2) - 2 * (wSer s (X * U) * V ^ 2)) ^ 2 =
      4 * (wSer s (X * U) * V ^ 2) ^ 3 - C a * X ^ 4 * (wSer s (X * U) * V ^ 2) - C b * X ^ 6 := by
  unfold OdeSer at h
  set P := wSer s (X * U) * V ^ 2 with hP
  have hW : wSer s (X * U) = P * U ^ 2 := by
    rw [hP, mul_assoc, ← mul_pow, mul_comm V, hUV]; simp
  have hU : U ≠ 0 := left_ne_zero_of_mul_eq_one hUV
  rw [hW] at h
  simp only [Derivation.leibniz, Derivation.leibniz_pow, derivative_X, smul_eq_mul,
    nsmul_eq_mul] at h
  apply mul_left_cancel₀ (pow_ne_zero 6 hU)
  push_cast at h
  linear_combination h

lemma theta_unique {s a b : ℂ} {A B : ℂ⟦X⟧} (hA0 : coeff 0 A = 0) (hA1 : coeff 1 A = 1)
    (hA2 : coeff 2 A = 0) (hB0 : coeff 0 B = 0) (hB1 : coeff 1 B = 1) (hB2 : coeff 2 B = 0)
    (hA : OdeSer s a b A) (hB : OdeSer s a b B) : A = B := by
  obtain ⟨U, rfl⟩ : X ∣ A := X_dvd_iff.2 (by simpa using hA0)
  obtain ⟨T, rfl⟩ : X ∣ B := X_dvd_iff.2 (by simpa using hB0)
  rw [coeff_succ_X_mul] at hA1 hA2 hB1 hB2
  simp only [coeff_zero_eq_constantCoeff] at hA1 hB1
  have hUV : U * U⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hA1])
  have hTV : T * T⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hB1])
  have hV0 : constantCoeff U⁻¹ = 1 := by simp [hA1]
  have hV1 : constantCoeff T⁻¹ = 1 := by simp [hB1]
  generalize U⁻¹ = V at hUV hV0
  generalize T⁻¹ = Y at hTV hV1
  have hPQ := ode_unique (by simp [wSer, Derivation.leibniz, hA1, hV0])
    (by simp [wSer, Derivation.leibniz, hB1, hV1]) (ode_reduce hUV hA) (ode_reduce hTV hB)
  have dV : d⁄dX ℂ V = -V ^ 2 * d⁄dX ℂ U := by
    have := congrArg (d⁄dX ℂ) hUV
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at this
    linear_combination V * this - d⁄dX ℂ V * hUV
  have dY : d⁄dX ℂ Y = -Y ^ 2 * d⁄dX ℂ T := by
    have := congrArg (d⁄dX ℂ) hTV
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at this
    linear_combination Y * this - d⁄dX ℂ Y * hTV
  have h1 : d⁄dX ℂ U * V = d⁄dX ℂ T * Y := by
    refine derivative.ext ?_ ?_
    · apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := ℂ)))
      simp only [wSer, Derivation.leibniz, smul_eq_mul, derivative_X, map_add, mul_one] at hPQ ⊢
      rw [dV, dY]
      linear_combination -hPQ + ((U * V + 1) * (1 - C s * X ^ 2) - X ^ 2 * V * d⁄dX ℂ (d⁄dX ℂ U)) * hUV
        - ((T * Y + 1) * (1 - C s * X ^ 2) - X ^ 2 * Y * d⁄dX ℂ (d⁄dX ℂ T)) * hTV
    · have e : ∀ F : ℂ⟦X⟧, constantCoeff (d⁄dX ℂ F) = coeff 1 F := fun F => by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]; simp
      rw [map_mul, map_mul, e, e, hA2, hB2, zero_mul, zero_mul]
  have h2 : U * Y = 1 := by
    refine derivative.ext ?_ (by simp [hA1, hV1])
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero]
    rw [dY]
    linear_combination U * Y * h1 - Y * d⁄dX ℂ U * hUV
  have : U = T := by linear_combination T * h2 - U * hTV
  rw [this]

lemma coeff_two_mul' (f g : R⟦X⟧) : coeff 2 (f * g) =
    coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
  simp [coeff_mul, Finset.Nat.antidiagonal_succ]; ring

lemma coeff_one_mul' (f g : R⟦X⟧) : coeff 1 (f * g) =
    coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  simp [coeff_mul, Finset.Nat.antidiagonal_succ]

lemma coeff_zero_mul' (f g : R⟦X⟧) : coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  simp

lemma OdeSer.const_eq {s a b : ℂ} {A : ℂ⟦X⟧} (hA0 : coeff 0 A = 0) (hA1 : coeff 1 A = 1)
    (hA2 : coeff 2 A = 0) (hA : OdeSer s a b A) : s = -2 * coeff 3 A := by
  have w0 : coeff 0 (wSer s A) = 1 := by
    simp only [wSer, sq, map_sub, coeff_zero_mul', coeff_derivative, coeff_C_mul]
    simp [hA0, hA1]
  have w1 : coeff 1 (wSer s A) = 0 := by
    simp only [wSer, sq, map_sub, coeff_one_mul', coeff_derivative, coeff_C_mul]
    simp [hA0, hA1, hA2]
  have w2 : coeff 2 (wSer s A) = -s := by
    simp only [wSer, sq, map_sub, coeff_two_mul', coeff_derivative, coeff_C_mul]
    simp [hA0, hA1, hA2]; ring
  have h := congrArg (coeff 2) hA
  generalize wSer s A = W at h w0 w1 w2
  have e2 : (2 : ℂ⟦X⟧) = C 2 := rfl
  have e4 : (4 : ℂ⟦X⟧) = C 4 := rfl
  simp only [pow_succ, pow_zero, one_mul, e2, e4, mul_assoc, map_sub, coeff_C_mul, coeff_two_mul',
    coeff_one_mul', coeff_zero_mul', coeff_derivative, Nat.reduceAdd, hA0, hA1, hA2, w0, w1, w2] at h
  push_cast at h
  linear_combination (1 / 12 : ℂ) * h

end Formal

section Taylor

open PowerSeries

def Ent : Subring (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := differentiable_const 1
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := differentiable_const 0
  neg_mem' := fun hf => hf.neg

lemma Ent.diff (f : Ent) : Differentiable ℂ f.1 := f.2

lemma Ent.contDiff (f : Ent) (n : ℕ) : ContDiff ℂ n f.1 := (Ent.diff f).contDiff

def dE (f : Ent) : Ent :=
  ⟨deriv f.1, differentiableOn_univ.1 ((Ent.diff f).differentiableOn.deriv isOpen_univ)⟩

def cE (c : ℂ) : Ent := ⟨fun _ => c, differentiable_const c⟩

def sE (α : ℂ) (f : Ent) : Ent :=
  ⟨fun z => f.1 (α * z), (Ent.diff f).comp (differentiable_id.const_mul α)⟩

def tay : Ent →+* ℂ⟦X⟧ where
  toFun f := PowerSeries.mk (coef1 f.1)
  map_zero' := by ext n; simp [coef1]
  map_one' := by
    ext n
    cases n with
    | zero => simp [coef1]
    | succ n =>
      have : ((1 : Ent) : ℂ → ℂ) = fun _ => 1 := rfl
      rw [coeff_mk, coef1, this, iteratedDeriv_const]
      simp [coeff_one]
  map_add' f g := by
    ext n
    simp only [coeff_mk, map_add, coef1, Subring.coe_add]
    rw [iteratedDeriv_add (Ent.contDiff f n).contDiffAt (Ent.contDiff g n).contDiffAt, add_div]
  map_mul' f g := by
    ext n
    simp only [coeff_mk, coeff_mul, coef1, Subring.coe_mul]
    rw [iteratedDeriv_mul (Ent.contDiff f n).contDiffAt (Ent.contDiff g n).contDiffAt,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have h1 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have h2 : ((n - k).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
    have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [Nat.cast_choose ℂ hk']
    field_simp

lemma coeff_tay (f : Ent) (n : ℕ) : coeff n (tay f) = coef1 f.1 n := coeff_mk n (coef1 f.1)

lemma tay_dE (f : Ent) : tay (dE f) = d⁄dX ℂ (tay f) := by
  ext n
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  simp only [coeff_derivative, coeff_tay, coef1, dE, iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

lemma tay_cE (c : ℂ) : tay (cE c) = C c := by
  ext n
  cases n with
  | zero => simp [coeff_tay, coef1, cE]
  | succ n => simp [coeff_tay, coef1, cE, iteratedDeriv_const, coeff_C]

lemma tay_sE (α : ℂ) (f : Ent) : tay (sE α f) = rescale α (tay f) := by
  ext n
  simp only [coeff_rescale, coeff_tay, coef1, sE]
  rw [iteratedDeriv_comp_const_mul (Ent.contDiff f n)]
  simp [mul_div_assoc]

lemma tay_injective : Function.Injective tay := by
  intro f g h
  ext z
  rw [← Complex.taylorSeries_eq_of_entire' 0 z (Ent.diff f),
    ← Complex.taylorSeries_eq_of_entire' 0 z (Ent.diff g)]
  refine tsum_congr fun n => ?_
  have := congrArg (coeff n) h
  simp only [coeff_tay, coef1, div_eq_inv_mul] at this
  rw [this]

def wE (s : ℂ) (f : Ent) : Ent := dE f ^ 2 - f * dE (dE f) - cE s * f ^ 2

lemma tay_wE (s : ℂ) (f : Ent) : tay (wE s f) = wSer s (tay f) := by
  simp [wE, wSer, tay_dE, tay_cE]

lemma wE_apply (s : ℂ) (f : Ent) (z : ℂ) :
    (wE s f).1 z = deriv f.1 z ^ 2 - f.1 z * deriv (deriv f.1) z - s * f.1 z ^ 2 := by
  simp [wE, dE, cE]

lemma eq_of_eq_off (L : PeriodPair) {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z ∉ L.lattice, f z = g z) (z : ℂ) : f z = g z :=
  tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z)
    (hf.continuousAt.mono_left nhdsWithin_le_nhds) (hg.continuousAt.mono_left nhdsWithin_le_nhds)
    ((eventually_ne_notMem_periodLattice L z).mono h)

lemma Ent.ext_off (L : PeriodPair) {f g : Ent} (h : ∀ z ∉ L.lattice, f.1 z = g.1 z) : f = g :=
  Subtype.ext (funext (eq_of_eq_off L (Ent.diff f).continuous (Ent.diff g).continuous h))

lemma odeSer_tay (L : PeriodPair) {s : ℂ} {f : Ent}
    (h : ∀ z ∉ L.lattice, (wE s f).1 z = L.weierstrassP z * f.1 z ^ 2) :
    OdeSer s L.g₂ L.g₃ (tay f) := by
  have key : (dE (wE s f) * f - 2 * wE s f * dE f) ^ 2 =
      4 * wE s f ^ 3 - cE L.g₂ * wE s f * f ^ 4 - cE L.g₃ * f ^ 6 := by
    refine Ent.ext_off L fun z hz => ?_
    have h1 : HasDerivAt (wE s f).1
        (L.derivWeierstrassP z * f.1 z ^ 2 + L.weierstrassP z * (2 * f.1 z * deriv f.1 z)) z := by
      have := (hasDerivAt_weierstrassP L hz).mul ((Ent.diff f z).hasDerivAt.pow 2)
      refine HasDerivAt.congr_of_eventuallyEq (by simpa using this) ?_
      filter_upwards [eventually_notMem_periodLattice L hz] with w hw using h w hw
    have h2 := L.derivWeierstrassP_sq z hz
    have e2 : ((2 : Ent) : ℂ → ℂ) z = 2 := rfl
    have e4 : ((4 : Ent) : ℂ → ℂ) z = 4 := rfl
    simp only [dE, cE, Subring.coe_pow, AddSubgroupClass.coe_sub, Subring.coe_mul, Pi.pow_apply,
      Pi.sub_apply, Pi.mul_apply, e2, e4, h1.deriv, h z hz]
    linear_combination f.1 z ^ 6 * h2
  have := congrArg tay key
  simpa [OdeSer, tay_dE, tay_cE, tay_wE, map_ofNat] using this

lemma endSer_tay_iff (L : PeriodPair) {s α : ℂ} {f : Ent} {N m : ℕ} {q : ℕ → ℂ}
    (h : ∀ z ∉ L.lattice, (wE s f).1 z = L.weierstrassP z * f.1 z ^ 2)
    (h0 : ∀ z ∉ L.lattice, f.1 z ≠ 0) :
    EndSer α N m q s (tay f) ↔ ∀ z ∉ L.lattice, f.1 (α * z) ^ 2 =
      f.1 z ^ (2 * N) * ∑ k ∈ Finset.range (m + 1), q k * L.weierstrassP z ^ k := by
  have e : EndSer α N m q s (tay f) ↔ sE α f ^ 2 * f ^ (2 * m) = f ^ (2 * N) *
      ∑ k ∈ Finset.range (m + 1), cE (q k) * (wE s f ^ k * f ^ (2 * (m - k))) := by
    rw [← tay_injective.eq_iff]
    simp [EndSer, homSer, tay_sE, tay_cE, tay_wE]
  have e2 : ∀ z ∉ L.lattice,
      (∑ k ∈ Finset.range (m + 1), cE (q k) * (wE s f ^ k * f ^ (2 * (m - k))) : Ent).1 z =
      (∑ k ∈ Finset.range (m + 1), q k * L.weierstrassP z ^ k) * f.1 z ^ (2 * m) := by
    intro z hz
    rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    simp only [cE, Subring.coe_pow, Subring.coe_mul, Pi.pow_apply, Pi.mul_apply, h z hz,
      Nat.add_sub_cancel_left]
    ring
  rw [e]
  constructor
  · intro H z hz
    have := congrArg (fun g : Ent => g.1 z) H
    simp only [Subring.coe_pow, Subring.coe_mul, Pi.pow_apply, Pi.mul_apply, e2 z hz, sE] at this
    exact mul_right_cancel₀ (pow_ne_zero (2 * m) (h0 z hz)) (by rw [this]; ring)
  · intro H
    refine Ent.ext_off L fun z hz => ?_
    simp only [Subring.coe_pow, Subring.coe_mul, Pi.pow_apply, Pi.mul_apply, e2 z hz, sE, H z hz]
    ring

def twist (c : ℂ) (f : Ent) : Ent :=
  ⟨fun z => f.1 z * Complex.exp (c * z ^ 2), by
    have := Ent.diff f
    change Differentiable ℂ _
    fun_prop⟩

lemma deriv_twist (c : ℂ) (f : Ent) : deriv (twist c f).1 =
    fun z => (deriv f.1 z + 2 * c * z * f.1 z) * Complex.exp (c * z ^ 2) := by
  funext z
  have := (Ent.diff f z).hasDerivAt.mul (((hasDerivAt_pow 2 z).const_mul c).cexp)
  refine (HasDerivAt.deriv this).trans ?_
  simp; ring

lemma wE_twist (s c : ℂ) (f : Ent) (z : ℂ) :
    (wE (s - 2 * c) (twist c f)).1 z = (wE s f).1 z * Complex.exp (c * z ^ 2) ^ 2 := by
  have := ((Ent.diff (dE f) z).hasDerivAt.add
    (((hasDerivAt_id z).const_mul (2 * c)).mul (Ent.diff f z).hasDerivAt)).mul
      (((hasDerivAt_pow 2 z).const_mul c).cexp)
  have h2 : deriv (fun z => (deriv f.1 z + 2 * c * z * f.1 z) * Complex.exp (c * z ^ 2)) z = _ :=
    HasDerivAt.deriv this
  rw [wE_apply, wE_apply, deriv_twist, h2]
  simp [twist, dE]; ring

lemma coeff_tay_of_odd {f : Ent} (h1 : deriv f.1 0 = 1) (ho : ∀ z, f.1 (-z) = -f.1 z) :
    coeff 0 (tay f) = 0 ∧ coeff 1 (tay f) = 1 ∧ coeff 2 (tay f) = 0 := by
  have e : sE (-1) f = -f := by ext z; simp [sE, ho]
  have := congrArg tay e
  rw [tay_sE, map_neg] at this
  have e0 := congrArg (coeff 0) this
  have e2 := congrArg (coeff 2) this
  simp only [coeff_rescale, map_neg] at e0 e2
  exact ⟨by linear_combination e0 / 2, by simp [coeff_tay, coef1, h1], by linear_combination e2 / 2⟩

end Taylor

section Lattice

variable (L : PeriodPair)

lemma exists_wE {f : Ent} (h00 : f.1 0 = 0) (h1 : deriv f.1 0 = 1) (h0 : ∀ z ∉ L.lattice, f.1 z ≠ 0)
    (hadd : ∀ u ∉ L.lattice, ∀ v ∉ L.lattice, (L.weierstrassP u - L.weierstrassP v) *
      (f.1 u ^ 2 * f.1 v ^ 2) = -(f.1 (u + v) * f.1 (u - v))) :
    ∃ s, ∀ z ∉ L.lattice, (wE s f).1 z = L.weierstrassP z * f.1 z ^ 2 := by
  have hf := Ent.diff f
  have hfc := hf.continuous
  have hf' : Differentiable ℂ (deriv f.1) := Ent.diff (dE f)
  let φ : ℂ → ℂ → ℂ := fun u v =>
    f.1 (u + v) * f.1 (u - v) + L.weierstrassP u * f.1 u ^ 2 * f.1 v ^ 2
  let φ' : ℂ → ℂ → ℂ := fun u v => deriv f.1 (u + v) * f.1 (u - v) - f.1 (u + v) * deriv f.1 (u - v)
    + L.weierstrassP u * f.1 u ^ 2 * (2 * f.1 v * deriv f.1 v)
  have p : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ u v,
      HasDerivAt (fun v => g (u + v)) (deriv g (u + v)) v := fun hg u v =>
    (hg _).hasDerivAt.comp_const_add u v
  have q : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ u v,
      HasDerivAt (fun v => g (u - v)) (-deriv g (u - v)) v := fun hg u v =>
    (hg _).hasDerivAt.comp_const_sub u v
  have d1 : ∀ u v, HasDerivAt (φ u) (φ' u v) v := fun u v => by
    have := ((p hf u v).mul (q hf u v)).add
      (((hf v).hasDerivAt.pow 2).const_mul (L.weierstrassP u * f.1 u ^ 2))
    refine HasDerivAt.congr_deriv this ?_
    simp [φ']; ring
  have d2 : ∀ u, HasDerivAt (φ' u) (2 * (f.1 u * deriv (deriv f.1) u - deriv f.1 u ^ 2 +
      L.weierstrassP u * f.1 u ^ 2)) 0 := fun u => by
    have := (((p hf' u 0).mul (q hf u 0)).sub ((p hf u 0).mul (q hf' u 0))).add
      ((((hf 0).hasDerivAt.const_mul 2).mul (hf' 0).hasDerivAt).const_mul
        (L.weierstrassP u * f.1 u ^ 2))
    refine HasDerivAt.congr_deriv this ?_
    simp [h00, h1]; ring
  obtain ⟨u₀, hu₀⟩ := (eventually_ne_notMem_periodLattice L 0).exists
  refine ⟨-(f.1 u₀ * deriv (deriv f.1) u₀ - deriv f.1 u₀ ^ 2 + L.weierstrassP u₀ * f.1 u₀ ^ 2) /
    f.1 u₀ ^ 2, fun u hu => ?_⟩
  have e0 : (fun v => f.1 u₀ ^ 2 * φ u v) = fun v => f.1 u ^ 2 * φ u₀ v :=
    funext (eq_of_eq_off L (by simp only [φ]; fun_prop) (by simp only [φ]; fun_prop) fun v hv => by
      simp only [φ]
      linear_combination f.1 u₀ ^ 2 * hadd u hu v hv - f.1 u ^ 2 * hadd u₀ hu₀ v hv)
  have e1 : (fun v => f.1 u₀ ^ 2 * φ' u v) = fun v => f.1 u ^ 2 * φ' u₀ v :=
    funext fun v => ((d1 u v).const_mul _).unique (e0 ▸ (d1 u₀ v).const_mul _)
  have e2 := ((d2 u).const_mul (f.1 u₀ ^ 2)).unique (e1 ▸ (d2 u₀).const_mul _)
  have := h0 u₀ hu₀
  rw [wE_apply]
  field_simp
  linear_combination (-1 / 2 : ℂ) * e2

variable {L} {f : ℂ → ℂ} {k α : ℂ} {N : ℕ}

lemma exp_scale (hα : α * (starRingEnd ℂ) α = N) (z ω : ℂ) :
    Complex.exp (k * (2 * (α * z) + α * ω) * (starRingEnd ℂ) (α * ω)) =
      Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω) ^ N := by
  rw [← Complex.exp_nat_mul, ← hα, map_mul]
  congr 1; ring

lemma exists_poly (hf : Differentiable ℂ f) (h0 : ∀ z, f z = 0 ↔ z ∈ L.lattice)
    (ho : ∀ z, f (-z) = -f z)
    (hp : ∀ ω ∈ L.lattice, ∀ z, f (z + ω) ^ 2 =
      f z ^ 2 * Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω))
    (hα : α * (starRingEnd ℂ) α = N) (hL : ∀ ω ∈ L.lattice, α * ω ∈ L.lattice) :
    ∃ (m : ℕ) (q : ℕ → ℂ), ∀ z ∉ L.lattice, f (α * z) ^ 2 =
      f z ^ (2 * N) * ∑ j ∈ Finset.range (m + 1), q j * L.weierstrassP z ^ j := by
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L
    (g := fun z => f (α * z) ^ 2 / f z ^ (2 * N))
    (by
      have h1 : AnalyticAt ℂ (fun z => f (α * z) ^ 2) 0 :=
        (show Differentiable ℂ (fun z => f (α * z) ^ 2) by fun_prop).analyticAt 0
      have h2 : AnalyticAt ℂ (fun z => f z ^ (2 * N)) 0 :=
        (show Differentiable ℂ (fun z => f z ^ (2 * N)) by fun_prop).analyticAt 0
      exact h1.meromorphicAt.div h2.meromorphicAt)
    (fun z hz => DifferentiableAt.div (by fun_prop) (by fun_prop)
      (pow_ne_zero _ fun h => hz ((h0 z).1 h)))
    (fun z ω hω => by
      simp only [pow_mul]
      rw [mul_add, hp _ (hL ω hω), hp ω hω, exp_scale hα, mul_pow,
        mul_div_mul_right _ _ (pow_ne_zero _ (Complex.exp_ne_zero _))])
    (fun z => by simp [ho, pow_mul])
  refine ⟨A.natDegree, A.coeff, fun z hz => ?_⟩
  rw [← Polynomial.eval_eq_sum_range, ← hA z hz,
    mul_div_cancel₀ _ (pow_ne_zero _ fun h => hz ((h0 z).1 h))]

lemma twist_eq_zero (hf : Differentiable ℂ f) (h0 : ∀ z, f z = 0 ↔ z ∈ L.lattice)
    (hp : ∀ ω ∈ L.lattice, ∀ z, f (z + ω) ^ 2 =
      f z ^ 2 * Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω))
    (hα : α * (starRingEnd ℂ) α = N) (hα0 : α ≠ 0) (hαN : α ^ 2 ≠ N) {c : ℂ} {R : ℂ → ℂ}
    (h : ∀ z ∉ L.lattice, (f (α * z) * Complex.exp (c * (α * z) ^ 2)) ^ 2 =
      (f z * Complex.exp (c * z ^ 2)) ^ (2 * N) * R (L.weierstrassP z)) : c = 0 := by
  have hfc := hf.continuous
  set κ : ℂ := 2 * c * (α ^ 2 - N) with hκ
  have h1 : ∀ z ∉ L.lattice, f (α * z) ^ 2 * Complex.exp (κ * z ^ 2) =
      (f z ^ 2) ^ N * R (L.weierstrassP z) := fun z hz => by
    apply mul_right_cancel₀ (pow_ne_zero (2 * N) (Complex.exp_ne_zero (c * z ^ 2)))
    have e : Complex.exp (κ * z ^ 2) * Complex.exp (c * z ^ 2) ^ (2 * N) =
        Complex.exp (c * (α * z) ^ 2) ^ 2 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; rw [hκ]; push_cast; ring
    have := h z hz
    rw [mul_pow, ← e, mul_pow (f z)] at this
    rw [← pow_mul]
    linear_combination this
  have h2 : ∀ ω ∈ L.lattice, ∀ z, f (α * (z + ω)) ^ 2 * Complex.exp (κ * (z + ω) ^ 2) =
      f (α * z) ^ 2 * Complex.exp (κ * z ^ 2) *
        Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω) ^ N := fun ω hω =>
    eq_of_eq_off L (by fun_prop) (by fun_prop) fun z hz => by
      rw [h1 z hz, h1 _ (fun h => hz (by simpa using sub_mem h hω)), hp ω hω,
        L.weierstrassP_add_coe z ⟨ω, hω⟩]
      ring
  have hω := L.ω₁_mem_lattice
  have hω0 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  generalize L.ω₁ = ω at hω hω0
  have h3 : α * ω ∈ L.lattice := by
    have := h2 ω hω 0
    simpa [(h0 0).2 (zero_mem _), h0] using this
  have h4 : ∀ w, Complex.exp (κ * (w / α + ω) ^ 2) = Complex.exp (κ * (w / α) ^ 2) :=
    eq_of_eq_off L (by fun_prop) (by fun_prop) fun w hw => by
      have e := h2 ω hω (w / α)
      rw [mul_add, hp _ h3, exp_scale hα, mul_div_cancel₀ _ hα0] at e
      apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 fun h => hw ((h0 w).1 h))
        (pow_ne_zero N (Complex.exp_ne_zero (k * (2 * (w / α) + ω) * (starRingEnd ℂ) ω))))
      linear_combination e
  by_contra hc
  have hκ0 : κ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) (sub_ne_zero.2 hαN)
  have h5 := h4 (α * ((Real.pi * Complex.I / (κ * ω) - ω) / 2))
  rw [mul_div_cancel_left₀ _ hα0] at h5
  have e : κ * ((Real.pi * Complex.I / (κ * ω) - ω) / 2 + ω) ^ 2 =
      κ * ((Real.pi * Complex.I / (κ * ω) - ω) / 2) ^ 2 + Real.pi * Complex.I := by
    field_simp; ring
  rw [e, Complex.exp_add_pi_mul_I] at h5
  exact Complex.exp_ne_zero _ (CharZero.neg_eq_self_iff.1 h5)

lemma sgStar_facts (L : PeriodPair) (Λ : AddSubgroup ℂ) (hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    ∃ (f : Ent) (s k : ℂ), f.1 = sgStar Λ ∧ deriv f.1 0 = 1 ∧ (∀ z, f.1 (-z) = -f.1 z) ∧
      (∀ z, f.1 z = 0 ↔ z ∈ L.lattice) ∧
      (∀ ω ∈ L.lattice, ∀ z, f.1 (z + ω) ^ 2 =
        f.1 z ^ 2 * Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω)) ∧
      ∀ z ∉ L.lattice, (wE s f).1 z = L.weierstrassP z * f.1 z ^ 2 := by
  obtain ⟨⟨hd, hd1, hodd, hU⟩, hzero, -, hwp, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ
    ⟨L.ω₁, L.ω₂, L.indep, by
      ext z
      rw [hL, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
      simp⟩
  obtain ⟨-, -, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  obtain ⟨s, hs⟩ := exists_wE L (f := ⟨sgStar Λ, hd⟩) ((hzero 0).2 Λ.zero_mem) hd1
    (fun z hz h => hz ((hL z).1 ((hzero z).1 h))) (fun u hu v hv => by
      have hu' : u ∉ Λ := fun h => hu ((hL u).1 h)
      have hv' : v ∉ Λ := fun h => hv ((hL v).1 h)
      rw [← (hw u hu').1, ← (hw v hv').1]
      exact hwp u v hu' hv')
  refine ⟨⟨sgStar Λ, hd⟩, s, Real.pi / area Λ, rfl, hd1, hodd, fun z => (hzero z).trans (hL z),
    fun ω hω z => ?_, hs⟩
  have e := congrArg (· ^ 2) (hU ω ((hL ω).2 hω) z)
  have e1 : ((if ω / 2 ∈ Λ then 1 else -1 : ℂ)) ^ 2 = 1 := by split_ifs <;> norm_num
  simp only [U1, mul_pow, e1, one_mul] at e
  change sgStar Λ (z + ω) ^ 2 = sgStar Λ z ^ 2 * _
  rw [← e, mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have : ((2 : ℕ) : ℂ) * (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
      (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) +
      Real.pi / area Λ * (2 * z + ω) * (starRingEnd ℂ) ω = 0 := by
    push_cast; ring
  rw [this, Complex.exp_zero, mul_one]

end Lattice

lemma liftM_coe (M : IntermediateField ℚ ℂ) (x : M) : liftM M (x : ℂ) = x := by
  simp [TaylorLogMetric.liftM]

lemma coe_liftM {M : IntermediateField ℚ ℂ} {x : ℂ} (hx : x ∈ M) : (liftM M x : ℂ) = x := by
  simp [TaylorLogMetric.liftM, hx]

theorem conj_sgStar (L : PeriodPair) (Λ : AddSubgroup ℂ) (hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {α : ℂ} {N : ℕ} (hαM : α ∈ M)
    (hρ : cj M ρ α = α) (hα : α * (starRingEnd ℂ) α = N) (hα0 : α ≠ 0) (hαN : α ^ 2 ≠ N)
    (hαL : ∀ ω ∈ Λ, α * ω ∈ Λ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M)
    (hc : ∀ n, coef1 (sgStar Λ) n ∈ M) (n : ℕ) :
    cj M ρ (coef1 (sgStar Λ) n) = coef1 (sgStar (lamConj M ρ Λ)) n := by
  obtain ⟨e2, e3, hΔ, -, -, -, hex⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  obtain ⟨L', a2, a3⟩ := hex (ρ (liftM M (g2 Λ))) (ρ (liftM M (g3 Λ))) (by
    have : (liftM M (g2 Λ)) ^ 3 - 27 * (liftM M (g3 Λ)) ^ 2 ≠ 0 := fun h => hΔ (by
      have := congrArg (algebraMap M ℂ) h
      simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero] at this
      simpa [coe_liftM h2, coe_liftM h3, TaylorLogMetric.discr] using this)
    have := (map_ne_zero ρ).2 this
    simpa [map_ofNat] using this)
  obtain ⟨b2, b3, -, -, -, huniq, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L'
    L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hspec : g2 (lamConj M ρ Λ) = ρ (liftM M (g2 Λ)) ∧ g3 (lamConj M ρ Λ) = ρ (liftM M (g3 Λ)) :=
    Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
      g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)))
      ⟨L'.lattice.toAddSubgroup, b2.trans a2, b3.trans a3⟩
  have hL' : ∀ z, z ∈ lamConj M ρ Λ ↔ z ∈ L'.lattice := fun z => by
    rw [huniq _ (hspec.1.trans (b2.trans a2).symm) (hspec.2.trans (b3.trans a3).symm)]
    rfl
  obtain ⟨f, s, k, hf, f1, fo, f0, fp, fw⟩ := sgStar_facts L Λ hL
  obtain ⟨g, s', k', hg, g1, go, g0, gp, gw⟩ := sgStar_facts L' _ hL'
  rw [← hf] at hc ⊢
  rw [← hg]
  let A : PowerSeries M := PowerSeries.mk fun n => liftM M (coef1 f.1 n)
  have hA : PowerSeries.map (algebraMap M ℂ) A = tay f := by
    ext n; simp [A, coeff_tay, coe_liftM (hc n)]
  obtain ⟨c0, c1, c2⟩ := coeff_tay_of_odd f1 fo
  have ode := odeSer_tay L fw
  have hs : s ∈ M := by
    rw [ode.const_eq c0 c1 c2, coeff_tay]
    exact mul_mem (neg_mem (ofNat_mem M 2)) (hc 3)
  obtain ⟨m, q, hq⟩ := exists_poly (Ent.diff f) f0 fo fp hα
    (fun ω hω => (hL _).1 (hαL ω ((hL _).2 hω)))
  have en := (endSer_tay_iff L fw (fun z hz h => hz ((f0 z).1 h))).2 hq
  have ι : ∀ {x : ℂ}, x ∈ M → algebraMap M ℂ (liftM M x) = x := fun hx => coe_liftM hx
  rw [← hA, ← ι hs, ← e2, ← e3, ← ι h2, ← ι h3] at ode
  rw [← hA, ← ι hs, ← ι hαM] at en
  obtain ⟨q', en'⟩ := en.descend
  have ode' := (ode.of_map _ (algebraMap M ℂ).injective).map (ρ : M →+* ℂ)
  have en'' := en'.map (ρ : M →+* ℂ)
  simp only [RingHom.coe_coe] at ode' en''
  rw [← a2, ← a3] at ode'
  rw [show ρ (liftM M α) = α from hρ] at en''
  obtain ⟨c, hcs⟩ : ∃ c, ρ (liftM M s) = s' - 2 * c := ⟨(s' - ρ (liftM M s)) / 2, by ring⟩
  rw [hcs] at ode' en''
  have tw : ∀ z ∉ L'.lattice, (wE (s' - 2 * c) (twist c g)).1 z =
      L'.weierstrassP z * (twist c g).1 z ^ 2 := fun z hz => by
    rw [wE_twist, gw z hz]; simp only [twist]; ring
  obtain ⟨t0, t1, t2⟩ := coeff_tay_of_odd (f := twist c g)
    (by simp [deriv_twist, g1]) (fun z => by simp [twist, go])
  have cA : ∀ n, PowerSeries.coeff n (PowerSeries.map (ρ : M →+* ℂ) A) = cj M ρ (coef1 f.1 n) :=
    fun n => by simp [A, cj]
  have l0 : liftM M 0 = 0 := liftM_coe M 0
  have l1 : liftM M 1 = 1 := liftM_coe M 1
  have eq := theta_unique (by rw [cA, ← coeff_tay, c0, cj, l0, map_zero])
    (by rw [cA, ← coeff_tay, c1, cj, l1, map_one]) (by rw [cA, ← coeff_tay, c2, cj, l0, map_zero])
    t0 t1 t2 ode' (odeSer_tay L' tw)
  rw [eq, endSer_tay_iff L' tw (fun z hz =>
    mul_ne_zero (fun h => hz ((g0 z).1 h)) (Complex.exp_ne_zero _))] at en''
  have hc0 : c = 0 := twist_eq_zero (Ent.diff g) g0 gp hα hα0 hαN
    (R := fun x => ∑ j ∈ Finset.range (m + 1), ρ (q' j) * x ^ j) en''
  rw [← cA, eq, coeff_tay, hc0]
  simp [twist]

theorem galSg_all : ∀ D : D7, galSg D := by
  intro D cc δ h M ρ hK h2 h3 hc n
  obtain ⟨⟨w₁, w₂, hw, he⟩, -, -, -, hcm⟩ :=
    GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h
  let L : PeriodPair := ⟨w₁, w₂, hw⟩
  have hL : ∀ z, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := fun z => by
    rw [he, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨b, hb⟩ : ∃ b : D.host.K, b ^ 2 = -(D.host.d : D.host.K) :=
    ⟨_, Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq)⟩
  have hbi : IsIntegral ℤ b := IsIntegral.of_pow two_pos (by
    rw [hb]; exact (isIntegral_natCast _).neg)
  have hd : (D.host.d : ℝ) ≠ 0 := by exact_mod_cast D.host.hyp.2.1.pos.ne'
  have hsq : D.host.φ₀ (b : D.host.E) ^ 2 = -(D.host.d : ℂ) := by
    have := congrArg (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) hb
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have hcm' := hcm ⟨b, hbi⟩
  have hK' := hK b
  change ∀ w ∈ _, D.host.φ₀ (b : D.host.E) * w ∈ _ at hcm'
  generalize D.host.φ₀ (b : D.host.E) = α at hsq hcm' hK'
  have hdc : (D.host.d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hn : α * (starRingEnd ℂ) α = D.host.d := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← norm_pow, hsq]
    simp
  exact conj_sgStar L _ hL M ρ hK'.1 hK'.2 hn (fun h0 => hdc (by simpa [h0] using hsq))
    (fun h0 => hdc (by linear_combination (hsq - h0) / 2)) hcm' h2 h3 hc n

end GlobalTheory.SigmaConj
