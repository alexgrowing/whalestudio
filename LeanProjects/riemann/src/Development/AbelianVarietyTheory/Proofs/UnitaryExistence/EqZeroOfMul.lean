import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CoefficientSpaceWeights
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeneralLinearGroupCharEqOneOfDetEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LFCompare
open Polynomial

section Rat
variable (K : Type) [Field K] [CharZero K]

def ratFn : Subalgebra K (ℚ → K) where
  carrier := {f | ∃ p q : K[X], (∀ s : ℚ, q.eval (s : K) ≠ 0) ∧ ∀ s : ℚ, f s * q.eval (s : K) = p.eval (s : K)}
  mul_mem' := by
    rintro f g ⟨p, q, hq, h⟩ ⟨p', q', hq', h'⟩
    refine ⟨p * p', q * q', fun s => by rw [eval_mul]; exact mul_ne_zero (hq s) (hq' s), fun s => ?_⟩
    rw [eval_mul, eval_mul, ← h, ← h', Pi.mul_apply]; ring
  add_mem' := by
    rintro f g ⟨p, q, hq, h⟩ ⟨p', q', hq', h'⟩
    refine ⟨p * q' + p' * q, q * q', fun s => by rw [eval_mul]; exact mul_ne_zero (hq s) (hq' s), fun s => ?_⟩
    rw [eval_add, eval_mul, eval_mul, eval_mul, ← h, ← h', Pi.add_apply]; ring
  algebraMap_mem' a := ⟨C a, 1, fun s => by simp, fun s => by simp⟩

variable {K}

theorem const_mem (a : K) : (fun _ : ℚ => a) ∈ ratFn K := (ratFn K).algebraMap_mem a

theorem cast_mem : (fun s : ℚ => (s : K)) ∈ ratFn K := ⟨X, 1, fun s => by simp, fun s => by simp⟩

theorem inv_mem {f : ℚ → K} (hf : f ∈ ratFn K) (h0 : ∀ s, f s ≠ 0) : (fun s => (f s)⁻¹) ∈ ratFn K := by
  obtain ⟨p, q, hq, h⟩ := hf
  refine ⟨q, p, fun s => by rw [← h]; exact mul_ne_zero (h0 s) (hq s), fun s => ?_⟩
  rw [← h, ← mul_assoc, inv_mul_cancel₀ (h0 s), one_mul]

theorem zpow_mem {f : ℚ → K} (hf : f ∈ ratFn K) (h0 : ∀ s, f s ≠ 0) (e : ℤ) : (fun s => f s ^ e) ∈ ratFn K := by
  obtain ⟨m, rfl | rfl⟩ := e.eq_nat_or_neg
  · simp only [zpow_natCast]
    exact pow_mem hf m
  · simp only [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem (inv_mem hf h0) m

theorem eq_zero_of_mul {f g : ℚ → K} (hf : f ∈ ratFn K) (hg : g ∈ ratFn K) (h : ∀ s, f s * g s = 0) {s₀ : ℚ}
    (h0 : g s₀ ≠ 0) (s : ℚ) : f s = 0 := by
  obtain ⟨p, q, hq, hp⟩ := hf
  obtain ⟨p', q', hq', hp'⟩ := hg
  have hpp : p * p' = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _
      ((Set.infinite_range_of_injective (Rat.cast_injective (α := K))).mono ?_)
    rintro _ ⟨t, rfl⟩
    change eval _ _ = 0
    rw [eval_mul, ← hp, ← hp']
    linear_combination (eval (t : K) q * eval (t : K) q') * h t
  have hp0 : p' ≠ 0 := by
    rintro rfl
    exact mul_ne_zero h0 (hq' s₀) (by simpa using hp' s₀)
  have : p = 0 := (mul_eq_zero.1 hpp).resolve_right hp0
  subst this
  exact (mul_eq_zero.1 (by simpa using hp s)).resolve_right (hq s)

theorem scalar_eq {c v f₀ g₀ f₁ g₁ : ℚ → K} {N : ℕ} (hN : N ≠ 0) (hv : v ∈ ratFn K) (hf₀ : f₀ ∈ ratFn K)
    (hg₀ : g₀ ∈ ratFn K) (hf₁ : f₁ ∈ ratFn K) (hg₁ : g₁ ∈ ratFn K) (e₀ : ∀ s, f₀ s = c s * g₀ s)
    (e₁ : ∀ s, f₁ s = c s * g₁ s) (hpow : ∀ s, c s ^ N = v s ^ N) (h0 : c 0 = v 0) (hv0 : v 0 ≠ 0)
    (hg0 : g₀ 0 ≠ 0) (hg1 : g₁ 1 ≠ 0) : c 1 = v 1 := by
  have hvg : (fun s => v s * g₀ s) ∈ ratFn K := mul_mem hv hg₀
  have hS : (fun s => ∑ i ∈ Finset.range N, f₀ s ^ i * (v s * g₀ s) ^ (N - 1 - i)) ∈ ratFn K := by
    have := Subalgebra.sum_mem (ratFn K) (t := Finset.range N)
      (f := fun i => f₀ ^ i * (fun s => v s * g₀ s) ^ (N - 1 - i))
      fun i _ => mul_mem (pow_mem hf₀ i) (pow_mem hvg _)
    convert this using 1
    funext s
    simp
  have a₀ : ∀ s, f₀ s - v s * g₀ s = 0 := by
    refine eq_zero_of_mul (s₀ := 0) (sub_mem hf₀ hvg) hS (fun s => ?_) ?_
    · rw [mul_comm]
      refine (geom_sum₂_mul _ _ _).trans ?_
      rw [e₀, mul_pow, mul_pow, hpow, sub_self]
    · have : f₀ 0 = v 0 * g₀ 0 := by rw [e₀, h0]
      simp only [this]
      rw [geom_sum₂_self]
      exact mul_ne_zero (Nat.cast_ne_zero.2 hN) (pow_ne_zero _ (mul_ne_zero hv0 hg0))
  have a₁ : f₁ 1 - v 1 * g₁ 1 = 0 := by
    refine eq_zero_of_mul (s₀ := 0) (f := fun s => f₁ s - v s * g₁ s) (sub_mem hf₁ (mul_mem hv hg₁)) hg₀
      (fun s => ?_) hg0 1
    have := a₀ s
    rw [e₀] at this
    rw [e₁]
    linear_combination g₁ s * this
  rw [e₁] at a₁
  exact mul_right_cancel₀ hg1 (sub_eq_zero.1 a₁)

theorem det_mem {n : Type} [Fintype n] [DecidableEq n] {M : ℚ → Matrix n n K}
    (h : ∀ i j, (fun s => M s i j) ∈ ratFn K) : (fun s => (M s).det) ∈ ratFn K := by
  have := Subalgebra.sum_mem (ratFn K) (t := Finset.univ)
    (f := fun σ : Equiv.Perm n => (fun _ : ℚ => ((Equiv.Perm.sign σ : ℤ) : K)) * ∏ i, fun s => M s (σ i) i)
    fun σ _ => mul_mem (const_mem _) (Subalgebra.prod_mem _ fun i _ => h _ _)
  convert this using 1
  funext s
  simp [Matrix.det_apply']

theorem matInv_mem {n : Type} [Fintype n] [DecidableEq n] {M : ℚ → Matrix n n K}
    (h : ∀ i j, (fun s => M s i j) ∈ ratFn K) (h0 : ∀ s, (M s).det ≠ 0) (i j : n) :
    (fun s => (M s)⁻¹ i j) ∈ ratFn K := by
  have h1 : (fun s => (M s).adjugate i j) ∈ ratFn K := by
    simp only [Matrix.adjugate_apply]
    refine det_mem fun a b => ?_
    by_cases hab : a = j
    · subst hab
      simpa using const_mem _
    · simpa [Matrix.updateRow_ne hab] using h a b
  have := mul_mem (inv_mem (det_mem h) h0) h1
  convert this using 1
  funext s
  simp [Matrix.inv_def]

theorem aeval_mem {σ σ' ι : Type} [Fintype ι] (r : ℚ → σ → ι → K) (y : σ → ι → σ')
    (hr : ∀ x j, (fun s => r s x j) ∈ ratFn K) (P : MvPolynomial σ K) (ℓ : MvPolynomial σ' K →ₗ[K] K) :
    (fun s => ℓ (MvPolynomial.aeval (fun x => ∑ j, MvPolynomial.C (r s x j) * MvPolynomial.X (y x j)) P)) ∈
      ratFn K := by
  induction P using MvPolynomial.induction_on generalizing ℓ with
  | C a => simpa using const_mem _
  | add p q hp hq =>
    simp only [map_add]
    exact add_mem (hp ℓ) (hq ℓ)
  | mul_X p x hp =>
    have := Subalgebra.sum_mem (ratFn K) (t := Finset.univ) fun j _ =>
      mul_mem (hr x j) (hp (ℓ ∘ₗ LinearMap.mulRight K (MvPolynomial.X (y x j))))
    convert this using 1
    funext s
    simp only [map_mul, MvPolynomial.aeval_X, Finset.mul_sum, map_sum, Finset.sum_apply, Pi.mul_apply,
      LinearMap.comp_apply, LinearMap.mulRight_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

end Rat

theorem tele {M : Type} [CommMonoid M] (x : ℕ → M) (ν : ℕ → ℕ) (hν : Antitone ν) (m : ℕ) :
    (∏ i ∈ Finset.range m, (∏ b ∈ Finset.range (i + 1), x b) ^ (ν i - ν (i + 1))) *
      (∏ b ∈ Finset.range m, x b) ^ ν m = ∏ b ∈ Finset.range m, x b ^ ν b := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, mul_assoc, ← pow_add, Nat.sub_add_cancel (hν (Nat.le_succ m)),
      Finset.prod_range_succ x, mul_pow, ← mul_assoc, ih, Finset.prod_range_succ]

theorem char_eq_one {F A n : Type} [Field F] [CharZero F] [CommGroup A] [Fintype n] [DecidableEq n]
    (ψ : GL n F →* A) (g : GL n F) (hg : (g : Matrix n n F).det = 1) : ψ g = 1 := by
  obtain ⟨L, L', D, hD, hM⟩ :=
    Matrix.SpecialLinearGroup.exists_list_transvec_mul_diagonal_mul_list_transvec ⟨(g : Matrix n n F), hg⟩
  let χ := ψ.comp (Matrix.SpecialLinearGroup.toGL (n := n) (R := F))
  have ht : ∀ t : Matrix.TransvectionStruct n F, χ t.toSpecialLinearGroup = 1 := by
    rintro ⟨i, j, hij, a⟩
    have hN : Matrix.single i j a * Matrix.single i j a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
    have := ddChar_unip_eq_one ψ _ hN (ddCharDiag (Pi.mulSingle i (Units.mk0 2 two_ne_zero))) 2 1
      (by
        ext a b
        by_cases h : i = a
        · subst h; simp [ddCharDiag_val]
        · simp [ddCharDiag_val, Matrix.single_apply, h])
      (by
        ext a b
        by_cases h : j = b
        · subst h; simp [ddCharDiag_val, Pi.mulSingle_eq_of_ne hij.symm]
        · simp [ddCharDiag_val, Matrix.single_apply, h])
      (by norm_num)
    rw [← this]
    exact congrArg ψ (Units.ext rfl)
  have hl : ∀ L : List (Matrix.TransvectionStruct n F),
      χ (L.map Matrix.TransvectionStruct.toSpecialLinearGroup).prod = 1 := fun L => by
    induction L with
    | nil => simp
    | cons t L ih => rw [List.map_cons, List.prod_cons, map_mul, ht, ih, one_mul]
  have hd : χ ⟨Matrix.diagonal D, hD⟩ = 1 :=
    ddChar_diag ψ _ (fun i j h => Matrix.diagonal_apply_ne D h) hD
  have := (congrArg χ hM).trans ((map_mul χ _ _).trans (congrArg₂ (· * ·) ((map_mul χ _ _).trans
    (congrArg₂ (· * ·) (hl L) hd)) (hl L')))
  have e : ψ g = χ ⟨(g : Matrix n n F), hg⟩ := congrArg ψ (Units.ext rfl)
  exact e.trans (this.trans (by simp))

section Cayley

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ}

theorem exists_curve (K : Type) [Field K] [CharZero K] (γ : Matrix (Fin n) (Fin n) E) (hγ : γᴴ * γ = 1)
    (h1 : IsUnit (1 + γ)) :
    ∃ Γ : ℚ → Matrix (Fin n) (Fin n) E, (∀ s, (Γ s)ᴴ * Γ s = 1) ∧ Γ 0 = 1 ∧ Γ 1 = γ ∧
      ∀ (σ : E →+* K) i j, (fun s => σ (Γ s i j)) ∈ ratFn K := by
  obtain ⟨w, hw⟩ := h1.exists_right_inv
  obtain ⟨hS, hS2⟩ := GenusSelfDual.cayley_skew (u := γ) hγ hw (mul_eq_one_comm.1 hw)
  generalize (1 - γ) * w = S at hS hS2
  have hs : ∀ s : ℚ, star (s • S) = -(s • S) := fun s => by rw [star_smul, hS, smul_neg]; rfl
  have hu : ∀ s : ℚ, IsUnit (1 + s • S).det := fun s =>
    (Matrix.isUnit_iff_isUnit_det _).1 (GenusSelfDual.isUnit_one_add_of_skew _ (hs s))
  refine ⟨fun s => 2 * (1 + s • S)⁻¹ - 1,
    fun s => GenusSelfDual.cayley_unitary (hs s) (Matrix.mul_nonsing_inv _ (hu s)), ?_, ?_, fun σ i j => ?_⟩
  · simp only [zero_smul, add_zero, inv_one]; norm_num
  · have h := Matrix.nonsing_inv_mul _ (hu 1)
    simp only [one_smul] at h ⊢
    have : (1 + S)⁻¹ * 2 = 1 + γ := by rw [← hS2, ← mul_assoc, h, one_mul]
    rw [two_mul, ← mul_two, this, add_sub_cancel_left]
  · have e : ∀ s : ℚ, σ.mapMatrix (1 + s • S)⁻¹ = (σ.mapMatrix (1 + s • S))⁻¹ := fun s =>
      (Matrix.inv_eq_right_inv (by rw [← map_mul, Matrix.mul_nonsing_inv _ (hu s), map_one])).symm
    have hm := matInv_mem (M := fun s : ℚ => σ.mapMatrix (1 + s • S)) (fun a b => by
      have := add_mem (const_mem (σ ((1 : Matrix (Fin n) (Fin n) E) a b))) (mul_mem cast_mem (const_mem (σ (S a b))))
      convert this using 1
      funext s
      simp [Rat.smul_def]) (fun s => by
        rw [← RingHom.map_det]; exact (_root_.map_ne_zero σ).2 (hu s).ne_zero) i j
    have := sub_mem (add_mem hm hm) (const_mem (σ ((1 : Matrix (Fin n) (Fin n) E) i j)))
    convert this using 1
    funext s
    simp only [Pi.sub_apply, Pi.add_apply, ← e]
    simp only [two_mul, Matrix.sub_apply, Matrix.add_apply, map_sub, map_add]
    rfl

theorem exists_scalar (γ : Matrix (Fin n) (Fin n) E) : ∃ z : E, star z * z = 1 ∧ IsUnit (1 + z • γ) := by
  obtain ⟨θ', h0, hθ⟩ := GenusSelfDual.exists_imaginary_integer E
  generalize (θ' : E) = θ at h0 hθ
  replace hθ : star θ = -θ := hθ
  have hc : ∀ k : ℤ, star (1 + k * θ) = 1 - k * θ := fun k => by
    rw [star_add, star_one, star_mul', star_intCast, hθ]; ring
  have hne : ∀ k : ℤ, 1 + k * θ ≠ 0 := fun k hk => by
    have := hc k
    rw [hk, star_zero] at this
    exact two_ne_zero (α := E) (by linear_combination hk - this)
  have hne' : ∀ k : ℤ, 1 - k * θ ≠ 0 := fun k => by
    rw [← hc]; exact star_ne_zero.2 (hne k)
  let f : ℤ → E := fun k => (1 - k * θ) / (1 + k * θ)
  have hf : Function.Injective f := fun a b hab => by
    rw [div_eq_div_iff (hne a) (hne b)] at hab
    have : (2 * θ : E) * (a - b) = 0 := by linear_combination -hab
    exact_mod_cast sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero h0))
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (Set.infinite_range_of_injective hf).exists_notMem_finite
    (GenusSelfDual.finite_not_isUnit_one_add_smul (RingHom.id E) γ)
  refine ⟨f k, ?_, not_not.1 hk⟩
  have := hc (-k)
  simp only [Int.cast_neg, neg_mul, ← sub_eq_add_neg, sub_neg_eq_add] at this
  simp only [f, star_div₀, hc, this]
  rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hne' k) (hne k))]

end Cayley

end GlobalTheory.LFCompare
