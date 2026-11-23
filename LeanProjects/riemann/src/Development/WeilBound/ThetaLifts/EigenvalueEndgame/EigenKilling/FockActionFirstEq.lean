import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

namespace PositivityTheory.ThKEnd.Comp

open MvPolynomial Formalism.BasicNotions.TH
open scoped Classical Matrix

section Core

variable {I C : Type} [Fintype I] [Fintype C]

def lin {σ : Type} [Fintype σ] : (σ → ℂ) →ₗ[ℂ] MvPolynomial σ ℂ := ∑ i, (LinearMap.proj i : (σ → ℂ) →ₗ[ℂ] ℂ).smulRight (X i)

theorem lin_apply {σ : Type} [Fintype σ] (u : σ → ℂ) : lin u = ∑ i, u i • (X i : MvPolynomial σ ℂ) := by
  simp [lin, LinearMap.sum_apply]

theorem pderiv_lin {σ : Type} [Fintype σ] (u : σ → ℂ) (j : σ) : pderiv j (lin u) = u j • (1 : MvPolynomial σ ℂ) := by
  simp [lin_apply, pderiv_X, Pi.single_apply]

theorem eq_zero_of_pow {σ : Type} [Fintype σ] (f : MvPolynomial σ ℂ) :
    ∀ l : MvPolynomial σ ℂ →ₗ[ℂ] ℂ, (∀ u n, l (lin u ^ n) = 0) → l f = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => intro l h; rw [← mul_one (MvPolynomial.C a), ← smul_eq_C_mul, map_smul, ← pow_zero (lin 0), h, smul_zero]
  | add p q hp hq => intro l h; rw [map_add, hp l h, hq l h, add_zero]
  | mul_X p i hp =>
    intro l h
    refine hp (l ∘ₗ LinearMap.mulRight ℂ (X i)) fun u n => ?_
    have hx : (X i : MvPolynomial σ ℂ) = lin (Pi.single i 1) := by simp [lin_apply, Pi.single_apply]
    let c : Polynomial ℂ := ∑ m ∈ Finset.range (n + 2), Polynomial.monomial m (l (X i ^ m * lin u ^ (n + 1 - m)) * (n + 1).choose m)
    have hc : c = 0 := Polynomial.funext fun s => by
      have := h (s • Pi.single i 1 + u) (n + 1)
      rw [map_add, map_smul, ← hx, add_pow, map_sum] at this
      rw [Polynomial.eval_zero, ← this, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Polynomial.eval_monomial, smul_pow, smul_mul_assoc, smul_mul_assoc, map_smul, ← nsmul_eq_mul' (X i ^ m * lin u ^ (n + 1 - m)), map_nsmul]
      simp [mul_comm, mul_left_comm]
    have h1 := congrArg (Polynomial.coeff · 1) hc
    simp only [c, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range] at h1
    have h2 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    simpa [h2, mul_comm] using h1

def der (p : C → Bool) (v w : I → ℂ) : Derivation ℂ (MvPolynomial (I × C) ℂ) (MvPolynomial (I × C) ℂ) :=
  ∑ a, ∑ b, ∑ c, (v a * w b) • (if p c then (X (a, c) : MvPolynomial (I × C) ℂ) • pderiv (b, c)
    else -((X (b, c) : MvPolynomial (I × C) ℂ) • pderiv (a, c)))

theorem der_apply (p : C → Bool) (v w : I → ℂ) (f : MvPolynomial (I × C) ℂ) : der p v w f =
    ∑ a, ∑ b, ∑ c, (v a * w b) • (if p c then X (a, c) * pderiv (b, c) f else -(X (b, c) * pderiv (a, c) f)) := by
  have hs : ∀ {ι : Type} [Fintype ι] (D : ι → Derivation ℂ (MvPolynomial (I × C) ℂ) (MvPolynomial (I × C) ℂ)),
      (∑ i, D i) f = ∑ i, D i f := fun D => by
    rw [← Finset.sum_apply]; exact congrFun (map_sum Derivation.coeFnAddMonoidHom D _) f
  simp only [der, hs, Derivation.smul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem der_neg (p : C → Bool) (v w : I → ℂ) (f) : der (fun c => !p c) v w f = -der p w v f := by
  rw [der_apply, der_apply, Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  cases p c <;> simp [mul_comm]

theorem der_lin (p : C → Bool) (v w : I → ℂ) (u : I × C → ℂ) : der p v w (lin u) =
    lin fun x => if p x.2 then v x.1 * ∑ b, w b * u (b, x.2) else -(w x.1 * ∑ a, v a * u (a, x.2)) := by
  have e : ∀ c, ∑ a, ∑ b, (v a * w b) • (if p c then X (a, c) * pderiv (b, c) (lin u) else -(X (b, c) * pderiv (a, c) (lin u))) =
      ∑ a, (if p c then v a * ∑ b, w b * u (b, c) else -(w a * ∑ b, v b * u (b, c))) • (X (a, c) : MvPolynomial (I × C) ℂ) := fun c => by
    simp only [pderiv_lin, mul_smul_comm, mul_one]
    cases p c
    · rw [Finset.sum_comm]
      simp only [Bool.false_eq_true, if_false, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_smul, smul_neg, neg_smul, smul_smul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by congr 2; ring
    · simp only [if_true, Finset.mul_sum, Finset.sum_smul, smul_smul, mul_assoc]
  rw [der_apply]
  refine Eq.trans ?_ (((Finset.sum_congr rfl fun c _ => e c).trans (Fintype.sum_prod_type_right' _).symm).trans (lin_apply _).symm)
  rw [Finset.sum_comm (γ := C)]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem core_pos (p : C → Bool) (S : I → Prop) (k : ℝ) (hk : 0 < k) (hc : Nat.card {c // p c} < Nat.card {a // S a})
    (l : MvPolynomial (I × C) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ v w : I → ℂ, (∀ a, ¬ S a → v a = 0 ∧ w a = 0) → ∑ a, v a * w a = 1 → ∀ f, l (der p v w f) = k * l f) : l = 0 := by
  refine LinearMap.ext fun f => eq_zero_of_pow f l fun u n => ?_
  let A : ({a // S a} → ℂ) →ₗ[ℂ] ({c // p c} → ℂ) := Matrix.vecMulLinear (Matrix.of fun a c => u (a.1, c.1))
  obtain ⟨w₀, hw₀, hne⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := A) (by simpa using hc))
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.1 hne
  let w : I → ℂ := fun a => if h : S a then w₀ ⟨a, h⟩ else 0
  let v : I → ℂ := Pi.single a₀.1 (w₀ a₀)⁻¹
  have hvw : ∑ a, v a * w a = 1 := by
    simp only [v, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, w, dif_pos a₀.2]
    exact inv_mul_cancel₀ ha₀
  have hwu : ∀ c, p c → ∑ b, w b * u (b, c) = 0 := fun c hc => by
    have := congrFun hw₀ ⟨c, hc⟩
    rw [← Fintype.sum_subtype_add_sum_subtype S, Finset.sum_eq_zero (s := Finset.univ) fun (b : {b // ¬ S b}) _ => by simp [w, b.2], add_zero]
    refine Eq.trans (Finset.sum_congr rfl (g := fun a => w₀ a * u (a.1, c)) fun a _ => by simp only [w, dif_pos a.2]) ?_
    simpa [A, Matrix.vecMul, dotProduct] using this
  let u' : I × C → ℂ := fun x => if p x.2 then 0 else w x.1 * ∑ a, v a * u (a, x.2)
  have d1 : der p v w (lin u) = -lin u' := by
    rw [der_lin, ← map_neg]
    congr 1
    funext x
    by_cases hx : p x.2 <;> simp [u', hx, hwu]
  have d2 : der p v w (lin u') = -lin u' := by
    rw [der_lin, ← map_neg]
    congr 1
    funext x
    by_cases hx : p x.2
    · simp [u', hx]
    · simp only [u', hx, Bool.false_eq_true, if_false, ← mul_assoc, ← Finset.sum_mul, hvw, one_mul, Pi.neg_apply]
  have d3 : der p v w (lin u - lin u') = 0 := by rw [map_sub, d1, d2, sub_self]
  have hl := h v w (fun a ha => ⟨Pi.single_eq_of_ne (fun e => ha (by rw [e]; exact a₀.2)) _, dif_neg ha⟩) hvw
  have key : ∀ i j : ℕ, l ((lin u - lin u') ^ i * lin u' ^ j) = 0 := fun i j => by
    have e : der p v w ((lin u - lin u') ^ i * lin u' ^ j) = -(j : ℂ) • ((lin u - lin u') ^ i * lin u' ^ j) := by
      rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, d3, d2]
      rcases j with _ | j
      · simp
      · simp only [smul_zero, add_zero, smul_eq_mul, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_C_mul, map_neg, map_natCast]
        ring
    have := hl ((lin u - lin u') ^ i * lin u' ^ j)
    rw [e, map_smul, smul_eq_mul] at this
    have h0 : (k : ℂ) + j ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < k + j).ne'
    exact (mul_eq_zero.1 (show ((k : ℂ) + j) * _ = 0 by linear_combination -this)).resolve_left h0
  rw [← sub_add_cancel (lin u) (lin u'), add_pow, map_sum]
  exact Finset.sum_eq_zero fun m _ => by rw [← nsmul_eq_mul', map_nsmul, key, smul_zero]

theorem core_neg (p : C → Bool) (S : I → Prop) (k : ℝ) (hk : k < 0) (hc : Nat.card {c // !p c} < Nat.card {a // S a})
    (l : MvPolynomial (I × C) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ v w : I → ℂ, (∀ a, ¬ S a → v a = 0 ∧ w a = 0) → ∑ a, v a * w a = 1 → ∀ f, l (der p v w f) = k * l f) : l = 0 :=
  core_pos (fun c => !p c) S (-k) (by linarith) hc l fun v w h1 h2 f => by
    rw [der_neg, map_neg, h w v (fun a ha => (h1 a ha).symm) (by simpa only [mul_comm] using h2)]
    simp

end Core

variable {P Q R S : ℕ}

theorem fockAction_first_eq (t : Bool) (v w : Ix P Q → ℂ) (h : ∀ a, ¬ a.isLeft = t → v a = 0 ∧ w a = 0) (h1 : ∑ a, v a * w a = 1) (f : Pol P Q R S) :
    fockAct1 P Q R S (Matrix.vecMulVec v w) f =
      der (fun c : Ix R S => c.isLeft == t) v w f + ((if t then ((R : ℝ) - S) / 2 else ((S : ℝ) - R) / 2 : ℝ) : ℂ) • f := by
  have e : fockAct1 P Q R S (Matrix.vecMulVec v w) f = ∑ a, ∑ b, ∑ c, (v a * w b) • omE (a, c) (b, c) f := by
    simp only [fockAct1, omAct, LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.sum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c (fun c' _ hc => by simp [Matrix.one_apply_ne hc.symm]) (by simp)]
    simp [Matrix.vecMulVec_apply]
  have e2 : ∀ a b c, (v a * w b) • omE (a, c) (b, c) f = (v a * w b) • (if (Sum.isLeft c == t) then X (a, c) * pderiv (b, c) f
      else -(X (b, c) * pderiv (a, c) f)) + (if a = b then v a * w a * (if (Sum.isLeft c == t) then 1 / 2 else -(1 / 2)) else 0 : ℂ) • f := fun a b c => by
    by_cases ha : a.isLeft = t
    swap
    · simp [(h a ha).1]
    by_cases hb : b.isLeft = t
    swap
    · by_cases e : a = b
      · exact absurd (e ▸ ha) hb
      · simp [(h b hb).2, e]
    have pa : linePos (a, c) = (Sum.isLeft c == t) := by subst ha; cases a <;> cases c <;> rfl
    have pb : linePos (b, c) = (Sum.isLeft c == t) := by subst hb; cases b <;> cases c <;> rfl
    simp only [omE, raiB, lowB, pa, pb, Prod.mk.injEq, and_true]
    by_cases e : a = b
    · subst e
      cases (Sum.isLeft c == t) <;> simp [smul_add, smul_smul] <;> module
    · have : (b, c) ≠ (a, c) := fun x => e (congrArg Prod.fst x).symm
      cases (Sum.isLeft c == t) <;> simp [e, pderiv_X_of_ne this]
  rw [e, der_apply]
  simp only [e2, Finset.sum_add_distrib, ← Finset.sum_smul]
  congr 2
  simp only [Finset.sum_comm (γ := Ix P Q) (α := Ix R S), Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum, ← Finset.sum_mul, h1]
  cases t <;> simp <;> ring

theorem noForm (m : ℤ) (hm : ((R + S : ℕ) : ℤ) < |m|) (hr : min R S < min P Q) (l : Pol P Q R S →ₗ[ℂ] ℂ)
    (h : ∀ Y : Mat P Q, IsKC Y → ∀ f, l (fockAct1 P Q R S Y f) = -((m : ℂ) / 2 * Y.trace) * l f) : l = 0 := by
  have key : ∀ t : Bool, ∀ v w : Ix P Q → ℂ, (∀ a, ¬ a.isLeft = t → v a = 0 ∧ w a = 0) → ∑ a, v a * w a = 1 → ∀ f,
      l (der (fun c : Ix R S => c.isLeft == t) v w f) =
        ((-((m : ℝ) / 2) - (if t then ((R : ℝ) - S) / 2 else ((S : ℝ) - R) / 2) : ℝ) : ℂ) * l f := fun t v w h0 h1 f => by
    have := h (Matrix.vecMulVec v w) (fun a b hab => by
      by_cases ha : a.isLeft = t
      · have : ¬ b.isLeft = t := fun hb => hab (by subst ha; cases a <;> cases b <;> simp_all [sameBlock])
        simp [Matrix.vecMulVec_apply, (h0 b this).2]
      · simp [Matrix.vecMulVec_apply, (h0 a ha).1]) f
    rw [fockAction_first_eq t v w h0 h1, map_add, map_smul, Matrix.trace_vecMulVec, dotProduct, h1, smul_eq_mul] at this
    rw [Complex.ofReal_sub]
    push_cast at this ⊢
    linear_combination this
  have cI : ∀ (A B : ℕ) (t : Bool), Nat.card {a : Ix A B // a.isLeft = t} = if t then A else B := fun A B t => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
    cases t <;> simp
  have c1 : ∀ t : Bool, Nat.card {c : Ix R S // c.isLeft == t} = if t then R else S := fun t => by
    rw [← cI]; exact Nat.card_congr (Equiv.subtypeEquivRight fun c => by simp)
  have c2 : ∀ t : Bool, Nat.card {c : Ix R S // !(c.isLeft == t)} = if t then S else R := fun t => by
    rw [show (if t then S else R) = if !t then R else S by cases t <;> rfl, ← cI]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => by cases t <;> cases c <;> simp)
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  rcases lt_abs.1 hm with h1 | h1
  · have h2 : (R : ℝ) + S < m := by exact_mod_cast h1
    rcases le_total R S with e | e
    · exact core_neg _ (fun a => a.isLeft = false) _ (by simp; linarith) (by rw [c2, cI]; simp; omega) l (key false)
    · exact core_neg _ (fun a => a.isLeft = true) _ (by simp; linarith) (by rw [c2, cI]; simp; omega) l (key true)
  · have h2 : (R : ℝ) + S < -m := by exact_mod_cast h1
    rcases le_total R S with e | e
    · exact core_pos _ (fun a => a.isLeft = true) _ (by simp; linarith) (by rw [c1, cI]; simp; omega) l (key true)
    · exact core_pos _ (fun a => a.isLeft = false) _ (by simp; linarith) (by rw [c1, cI]; simp; omega) l (key false)

end PositivityTheory.ThKEnd.Comp

end
